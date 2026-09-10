import GreedyLowerBound.ComparisonGrammar

set_option autoImplicit false
namespace GreedyLowerBound
open ComparisonIndex

theorem list_cost_flatMap {α β : Type} (xs : List α) (f : α → List β) (cost : β → Nat) :
    ((xs.flatMap f).map cost).sum = (xs.map (fun a => ((f a).map cost).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]

theorem comparisonTarget_rule_length (h : Nat) (D : List Bool) (s k : Nat) :
    (comparisonRhs h D (target s k)).length ≤ 65 := by
  simp only [comparisonRhs]
  split_ifs <;> simp

theorem comparisonTargets_cost (h : Nat) (D : List Bool) :
    ((comparisonTargets h D).map (fun x => (comparisonRhs h D x).length)).sum ≤ 130*h^2 := by
  unfold comparisonTargets
  rw [list_cost_flatMap]
  have hone : ∀ s, ((((List.range (2*h)).filter (fun k => decide (0 < prefixValue (chunk h D s) (k+1)))).map (target s)).map
      (fun x => (comparisonRhs h D x).length)).sum ≤ 130*h := by
    intro s
    let ks := (List.range (2*h)).filter (fun k => decide (0 < prefixValue (chunk h D s) (k+1)))
    have hc : ((ks.map (target s)).map (fun x => (comparisonRhs h D x).length)).sum ≤ ks.length*65 := by
      rw [List.map_map]
      calc
        _ ≤ (ks.map (fun _ => 65)).sum := List.sum_le_sum (fun k _ => comparisonTarget_rule_length h D s k)
        _ = _ := by simp [List.map_const']
    have hlen : ks.length ≤ 2*h := (List.length_filter_le _ _).trans (by simp)
    change ((ks.map (target s)).map (fun x => (comparisonRhs h D x).length)).sum ≤ _
    nlinarith
  calc
    _ ≤ ((List.range h).map (fun _ => 130*h)).sum := List.sum_le_sum (fun s _ => hone s)
    _ = _ := by simp [List.map_const', Nat.pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem comparisonPowers_cost (h : Nat) (D : List Bool) :
    ((comparisonPowers h).map (fun x => (comparisonRhs h D x).length)).sum = 64*h := by
  simp [comparisonPowers, List.map_map, Function.comp_def, comparisonRhs, List.map_const', Nat.mul_comm]

theorem comparisonAuxLayer_cost (h : Nat) (D : List Bool) (j u : Nat) :
    (((List.finRange 3).map (aux j u)).map (fun x => (comparisonRhs h D x).length)).sum =
      if u = 0 then 6 else 57 := by
  cases u <;> simp [List.map_map, Function.comp_def, comparisonRhs, mu_length, List.map_const']

theorem comparisonAuxLayers_cost (h : Nat) (D : List Bool) (j e : Nat) :
    (((List.range (e+1)).flatMap (fun u => (List.finRange 3).map (aux j u))).map
      (fun x => (comparisonRhs h D x).length)).sum = 6+57*e := by
  rw [list_cost_flatMap]
  simp only [comparisonAuxLayer_cost]
  rw [List.range_succ_eq_map]
  simp [List.map_map, Function.comp_def, List.map_const', Nat.mul_comm]

theorem comparisonAuxiliaries_cost (h : Nat) (D : List Bool) :
    ((comparisonAuxiliaries h).map (fun x => (comparisonRhs h D x).length)).sum =
      6*h + 57*(∑ j ∈ Finset.range h, auxiliaryExponent h (j+1)) := by
  rw [comparisonAuxiliaries, list_cost_flatMap]
  simp only [comparisonAuxLayers_cost]
  rw [sum_map_range_eq]
  simp [Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm]

/-- Equation (25), with the factor two kept integral. -/
theorem auxiliaryExponent_sum (h : Nat) :
    2*(∑ j ∈ Finset.range h, auxiliaryExponent h (j+1)) = 11*h^2+h := by
  have hsum : 2*(∑ j ∈ Finset.range h, j)+h = h^2 := by
    induction h with
    | zero => simp
    | succ h ih => rw [Finset.sum_range_succ]; nlinarith
  have he : (∑ j ∈ Finset.range h, auxiliaryExponent h (j+1)) +
      3*(∑ j ∈ Finset.range h, j)+h = 7*h*h := by
    calc
      _ = ∑ j ∈ Finset.range h, (auxiliaryExponent h (j+1)+3*j+1) := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ _j ∈ Finset.range h, 7*h := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj := Finset.mem_range.mp hj
        unfold auxiliaryExponent
        omega
      _ = _ := by simp [Nat.mul_comm]
  nlinarith

theorem comparisonStartRhs_length (h : Nat) (hh : 1 ≤ h) :
    (comparisonStartRhs h).length = 2*h^2+2*h-1 := by
  have hp : 1 ≤ h^2 := Nat.one_le_pow _ _ hh
  simp only [comparisonStartRhs, List.length_cons, interleaveRefs_length, comparisonRestRefs_length]
  omega

/-- The complete size count of the concrete comparison grammar. -/
theorem comparisonGrammar_size_bound (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) : 2*(comparisonGrammar h D hh hD).size ≤ 891*h^2+201*h-2 := by
  have ht := comparisonTargets_cost h D
  have hp := comparisonPowers_cost h D
  have ha := comparisonAuxiliaries_cost h D
  have hs := comparisonStartRhs_length h hh
  have he := auxiliaryExponent_sum h
  have hbound := list_rule_cost_bound (comparisonIndices h D) (fun x => (comparisonRhs h D x).length)
  have hc : (comparisonGrammar h D hh hD).size =
      ∑ i ∈ (comparisonIndices h D).toFinset, (comparisonRhs h D i).length :=
    (comparisonRecipe h D hh hD).compile_size _ ComparisonIndex.code_injective
  rw [← hc] at hbound
  simp only [comparisonIndices, List.map_append, List.sum_append, List.map_singleton,
    List.sum_cons, List.sum_nil, Nat.add_zero, comparisonRhs] at hbound
  change (comparisonGrammar h D hh hD).size ≤
    ((comparisonTargets h D).map (fun x => (comparisonRhs h D x).length)).sum +
    ((comparisonPowers h).map (fun x => (comparisonRhs h D x).length)).sum +
    ((comparisonAuxiliaries h).map (fun x => (comparisonRhs h D x).length)).sum +
    (comparisonStartRhs h).length at hbound
  rw [hp, ha, hs] at hbound
  have hsq : 1 ≤ h^2 := Nat.one_le_pow _ _ hh
  omega

theorem comparisonGrammar_size_le (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) : (comparisonGrammar h D hh hD).size ≤ 600*h^2 := by
  have hb := comparisonGrammar_size_bound h D hh hD
  have hs : h ≤ h^2 := by nlinarith
  omega

theorem input_minimumSize_upper (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) : Grammar.minimumSize (inputWord h D) ≤ 600*h^2 := by
  exact ((comparisonGrammar h D hh hD).minimumSize_le
    (comparisonGrammar_wellFormed h D hh hD) _ (comparisonGrammar_generates h D hh hD)).trans
      (comparisonGrammar_size_le h D hh hD)

end GreedyLowerBound
