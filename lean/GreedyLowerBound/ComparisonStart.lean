import GreedyLowerBound.ComparisonIndex

set_option autoImplicit false
namespace GreedyLowerBound
open ComparisonIndex

def comparisonTargetRefs (h : Nat) : List ComparisonIndex :=
  (List.range h).flatMap (fun s => (List.range h).map (fun i => target s (h+i)))

def comparisonAuxRefs (h : Nat) : List ComparisonIndex :=
  (List.range h).map (fun j => aux j (auxiliaryExponent h (j+1)) 0)

def comparisonRestRefs (h : Nat) : List ComparisonIndex :=
  (comparisonTargetRefs h).tail ++ comparisonAuxRefs h

/-- Insert the actual, consecutively numbered input separators. -/
def interleaveRefs {ι : Type} (base : Nat) : List ι → List (Nat ⊕ ι)
  | [] => []
  | i::is => Sum.inl base :: Sum.inr i :: interleaveRefs (base+1) is

def comparisonStartRhs (h : Nat) : List (Nat ⊕ ComparisonIndex) :=
  Sum.inr (target 0 h) :: interleaveRefs (1+3*h) (comparisonRestRefs h)

def comparisonValue (h : Nat) (D : List Bool) : ComparisonIndex → Word Nat
  | .target s k => List.replicate (prefixValue (chunk h D s) (k+1)) 0
  | .power j => List.replicate (64^(j+1)) 0
  | .aux j u c => comparisonAuxValue j u c
  | .start => inputWord h D

def comparisonInterpret (h : Nat) (D : List Bool) : Nat ⊕ ComparisonIndex → Word Nat :=
  Sum.elim (fun a => [a]) (comparisonValue h D)

@[simp] theorem comparisonInterpret_inl (h : Nat) (D : List Bool) (a : Nat) :
    comparisonInterpret h D (Sum.inl a) = [a] := rfl

@[simp] theorem comparisonInterpret_inr (h : Nat) (D : List Bool) (i : ComparisonIndex) :
    comparisonInterpret h D (Sum.inr i) = comparisonValue h D i := rfl

theorem comparisonTargetRefs_length (h : Nat) : (comparisonTargetRefs h).length = h^2 := by
  simp [comparisonTargetRefs, List.length_flatMap, List.map_map, Function.comp_def,
    List.map_const', Nat.pow_two]

theorem comparisonRestRefs_length (h : Nat) : (comparisonRestRefs h).length = h^2-1+h := by
  simp [comparisonRestRefs, comparisonTargetRefs_length, comparisonAuxRefs]

theorem interleaveRefs_length {ι : Type} (base : Nat) (is : List ι) :
    (interleaveRefs base is).length = 2*is.length := by
  induction is generalizing base with
  | nil => simp [interleaveRefs]
  | cons i is ih => simp [interleaveRefs, ih]; omega

theorem interleaveRefs_terminal {ι : Type} (base : Nat) (is : List ι) (a : Nat)
    (ha : Sum.inl a ∈ interleaveRefs base is) : base ≤ a ∧ a < base+is.length := by
  induction is generalizing base with
  | nil => simp [interleaveRefs] at ha
  | cons i is ih =>
    simp only [interleaveRefs, List.mem_cons, Sum.inl.injEq, Sum.inl_ne_inr, false_or] at ha
    rcases ha with rfl | ha
    · simp
    · have hh := ih (base+1) ha
      simp only [List.length_cons]
      omega

theorem interleaveRefs_reference {ι : Type} (base : Nat) (is : List ι) (i : ι) :
    Sum.inr i ∈ interleaveRefs base is ↔ i ∈ is := by
  induction is generalizing base with
  | nil => simp [interleaveRefs]
  | cons j is ih => simp [interleaveRefs, ih]

theorem interleaveRefs_expansion {ι : Type} (value : ι → Word Nat) (first : Word Nat)
    (base : Nat) (is : List ι) :
    first ++ (interleaveRefs base is).flatMap (Sum.elim (fun a => [a]) value) =
      joinFragments first (numberedRest base (is.map value)) := by
  induction is generalizing first base with
  | nil => simp [interleaveRefs, numberedRest, joinFragments]
  | cons i is ih =>
    simp only [interleaveRefs, List.flatMap_cons, List.singleton_append, List.map_cons, numberedRest]
    have hh := ih (value i) (base+1)
    change first ++ base :: (value i ++ _) = first ++ base :: joinFragments (value i) _
    rw [hh]

theorem comparisonTargetRefs_values (h : Nat) (D : List Bool) :
    (comparisonTargetRefs h).map (comparisonValue h D) =
      (targetNumbers h D).map (fun n => List.replicate n 0) := by
  simp only [comparisonTargetRefs, targetNumbers, List.map_flatMap, List.map_map]
  apply List.flatMap_congr
  intro s _
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_def, comparisonValue, targetNumber, prefixValue]
  have he : h+i+1 = h+1+i := by omega
  rw [he]

theorem comparisonRestRefs_values (h : Nat) (D : List Bool) :
    (comparisonRestRefs h).map (comparisonValue h D) = inputRest h D := by
  simp only [comparisonRestRefs, List.map_append, List.map_tail, comparisonTargetRefs_values,
    comparisonAuxRefs, List.map_map, inputRest]
  congr 1
  exact List.map_congr_left (fun j _ => comparisonAuxValue_final h j)

theorem comparisonTargetRefs_head (h : Nat) (hh : 1 ≤ h) :
    (comparisonTargetRefs h).head? = some (target 0 h) := by
  have he : h = (h-1)+1 := by omega
  conv_lhs => rw [comparisonTargetRefs, he, List.range_succ_eq_map]
  simp
  omega

theorem comparisonFirst_value (h : Nat) (D : List Bool) (hh : 1 ≤ h) :
    comparisonValue h D (target 0 h) = inputFirst h D := by
  have hhead := comparisonTargetRefs_head h hh
  have he := congrArg List.head? (comparisonTargetRefs_values h D)
  rw [List.head?_map, hhead] at he
  unfold inputFirst
  cases hn : targetNumbers h D with
  | nil => simp [hn] at he
  | cons n ns =>
    simp only [hn, List.map_cons, List.head?_cons, Option.map_some, Option.some.injEq] at he
    change some (comparisonValue h D (target 0 h)) = some (List.replicate n 0) at he
    exact Option.some.inj he

theorem comparisonStartRhs_expansion (h : Nat) (D : List Bool) (hh : 1 ≤ h) :
    (comparisonStartRhs h).flatMap (comparisonInterpret h D) = inputWord h D := by
  have he := interleaveRefs_expansion (comparisonValue h D)
    (comparisonValue h D (target 0 h)) (1+3*h) (comparisonRestRefs h)
  have ht : joinFragments (comparisonValue h D (target 0 h))
      (numberedRest (1+3*h) ((comparisonRestRefs h).map (comparisonValue h D))) = inputWord h D := by
    rw [comparisonFirst_value h D hh, comparisonRestRefs_values]
    rfl
  exact he.trans ht

end GreedyLowerBound
