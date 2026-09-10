import GreedyLowerBound.OptimalGrammar

set_option autoImplicit false
namespace GreedyLowerBound

/-- A finite symbolic SLP, with explicit expansion equations. Terminals are
natural names below cap; nonterminals can use any index type. This intermediate
format is compiled into the same Grammar type used for Greedy and the optimum. -/
structure GrammarRecipe (ι : Type) (cap : Nat) where
  defined : Finset ι
  rhs : ι → List (Nat ⊕ ι)
  value : ι → Word Nat
  start : ι
  start_mem : start ∈ defined
  rank : ι → Nat
  nonempty : ∀ i ∈ defined, rhs i ≠ []
  terminal_bound : ∀ i ∈ defined, ∀ a, Sum.inl a ∈ rhs i → a < cap
  reference : ∀ i ∈ defined, ∀ j, Sum.inr j ∈ rhs i → j ∈ defined ∧ rank j < rank i
  equation : ∀ i ∈ defined,
    value i = (rhs i).flatMap (Sum.elim (fun a => [a]) value)

namespace GrammarRecipe
variable {ι : Type} {cap : Nat}

def size (R : GrammarRecipe ι cap) : Nat := ∑ i ∈ R.defined, (R.rhs i).length

def name (code : ι → Nat) (i : ι) : Nat := cap+code i

def symbolName (code : ι → Nat) : Nat ⊕ ι → Nat
  | .inl a => a
  | .inr i => name (cap := cap) code i

theorem name_injective (code : ι → Nat) (hc : Function.Injective code) :
    Function.Injective (name (cap := cap) code) := by
  intro i j he
  exact hc (Nat.add_left_cancel he)

noncomputable def decode (R : GrammarRecipe ι cap) (code : ι → Nat) (a : Nat) : Option ι := by
  classical
  exact if h : ∃ i ∈ R.defined, name (cap := cap) code i = a then some h.choose else none

theorem decode_name (R : GrammarRecipe ι cap) (code : ι → Nat) (hc : Function.Injective code)
    (i : ι) (hi : i ∈ R.defined) : R.decode code (name (cap := cap) code i) = some i := by
  classical
  have hex : ∃ j ∈ R.defined, name (cap := cap) code j = name (cap := cap) code i := ⟨i, hi, rfl⟩
  simp only [decode, dif_pos hex]
  exact congrArg some (name_injective code hc hex.choose_spec.2)

theorem decode_some (R : GrammarRecipe ι cap) (code : ι → Nat) (a : Nat) (i : ι)
    (he : R.decode code a = some i) : i ∈ R.defined ∧ name (cap := cap) code i = a := by
  classical
  unfold decode at he
  split_ifs at he with hex
  · have hi : hex.choose = i := Option.some.inj he
    exact hi ▸ hex.choose_spec

theorem decode_terminal (R : GrammarRecipe ι cap) (code : ι → Nat) (a : Nat) (ha : a < cap) :
    R.decode code a = none := by
  classical
  have hn : ¬ ∃ i ∈ R.defined, name (cap := cap) code i = a := by
    rintro ⟨i, _, hi⟩
    unfold name at hi
    omega
  simp only [decode, dif_neg hn]

noncomputable def compile (R : GrammarRecipe ι cap) (code : ι → Nat) : Grammar where
  defined := R.defined.image (name (cap := cap) code)
  rhs := fun a => match R.decode code a with
    | none => []
    | some i => (R.rhs i).map (symbolName (cap := cap) code)
  start := name (cap := cap) code R.start

noncomputable def compiledValue (R : GrammarRecipe ι cap) (code : ι → Nat) (a : Nat) : Word Nat :=
  match R.decode code a with | none => [a] | some i => R.value i

theorem compiledValue_name (R : GrammarRecipe ι cap) (code : ι → Nat) (hc : Function.Injective code)
    (i : ι) (hi : i ∈ R.defined) : R.compiledValue code (name (cap := cap) code i) = R.value i := by
  simp only [compiledValue, R.decode_name code hc i hi]

theorem compiledValue_terminal (R : GrammarRecipe ι cap) (code : ι → Nat) (a : Nat)
    (ha : a < cap) : R.compiledValue code a = [a] := by
  simp only [compiledValue, R.decode_terminal code a ha]

theorem compile_rhs (R : GrammarRecipe ι cap) (code : ι → Nat) (hc : Function.Injective code)
    (i : ι) (hi : i ∈ R.defined) :
    (R.compile code).rhs (name (cap := cap) code i) = (R.rhs i).map (symbolName (cap := cap) code) := by
  simp only [compile, R.decode_name code hc i hi]

theorem compile_wellFormed (R : GrammarRecipe ι cap) (code : ι → Nat) (hc : Function.Injective code) :
    (R.compile code).WellFormed := by
  classical
  let rank := fun a => match R.decode code a with | none => 0 | some i => R.rank i
  refine ⟨Finset.mem_image.mpr ⟨R.start, R.start_mem, rfl⟩, ?_, rank, ?_⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    rw [R.compile_rhs code hc i hi]
    intro he
    exact R.nonempty i hi (List.map_eq_nil_iff.mp he)
  · intro a ha b hb hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    rw [R.compile_rhs code hc i hi] at hm
    obtain ⟨s, hs, he⟩ := List.mem_map.mp hm
    cases s with
    | inl t =>
      have ht := R.terminal_bound i hi t hs
      change t = cap+code j at he
      omega
    | inr k =>
      have hk : k = j := name_injective code hc he
      subst k
      have hr := (R.reference i hi j hs).2
      simpa only [rank, R.decode_name code hc i hi, R.decode_name code hc j hj] using hr

theorem compile_semantics (R : GrammarRecipe ι cap) (code : ι → Nat) (hc : Function.Injective code) :
    (R.compile code).Semantics (R.compiledValue code) := by
  classical
  constructor
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    rw [R.compiledValue_name code hc i hi, R.compile_rhs code hc i hi, List.flatMap_map, R.equation i hi]
    apply List.flatMap_congr
    intro s hs
    cases s with
    | inl a =>
      exact (R.compiledValue_terminal code a (R.terminal_bound i hi a hs)).symm
    | inr j =>
      exact (R.compiledValue_name code hc j (R.reference i hi j hs).1).symm
  · intro a ha
    have hd : R.decode code a = none := by
      cases he : R.decode code a with
      | none => rfl
      | some i =>
        have hi := R.decode_some code a i he
        exact False.elim (ha (Finset.mem_image.mpr ⟨i, hi.1, hi.2⟩))
    simp only [compiledValue, hd]

theorem compile_generates (R : GrammarRecipe ι cap) (code : ι → Nat) (hc : Function.Injective code) :
    (R.compile code).Generates (R.value R.start) := by
  exact ⟨R.compiledValue code, R.compile_semantics code hc,
    R.compiledValue_name code hc R.start R.start_mem⟩

theorem compile_size (R : GrammarRecipe ι cap) (code : ι → Nat) (hc : Function.Injective code) :
    (R.compile code).size = R.size := by
  classical
  unfold Grammar.size
  change (∑ a ∈ R.defined.image (name (cap := cap) code), ((R.compile code).rhs a).length) = _
  rw [Finset.sum_image (fun i _ j _ he => name_injective code hc he)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [R.compile_rhs code hc i hi, List.length_map]

/-- A symbolic comparison grammar yields a literal well-formed grammar of
exactly the same size, hence a valid upper bound on the actual optimum. -/
theorem minimumSize_le (R : GrammarRecipe ι cap) (code : ι → Nat) (hc : Function.Injective code) :
    Grammar.minimumSize (R.value R.start) ≤ R.size := by
  rw [← R.compile_size code hc]
  exact (R.compile code).minimumSize_le (R.compile_wellFormed code hc) _ (R.compile_generates code hc)

end GrammarRecipe
end GreedyLowerBound
