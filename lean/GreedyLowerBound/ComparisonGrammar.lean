import GreedyLowerBound.ComparisonRules

set_option autoImplicit false
namespace GreedyLowerBound
open ComparisonIndex

theorem comparisonRhs_equation (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) (x : ComparisonIndex) (hx : ComparisonValid h D x) :
    comparisonValue h D x = (comparisonRhs h D x).flatMap (comparisonInterpret h D) := by
  cases x with
  | target s k =>
    have hs : s < h ∧ k < 2*h ∧ 0 < prefixValue (chunk h D s) (k+1) := hx
    have hk : k < (chunk h D s).length := by rw [chunk_length h D s hD hs.1]; exact hs.2.1
    by_cases hp : prefixValue (chunk h D s) k = 0
    · have hstep := prefixValue_step_getD (chunk h D s) k hk
      have hv : prefixValue (chunk h D s) (k+1) = 1 := by
        rw [hp] at hstep
        cases hb : ((chunk h D s)[k]?).getD false <;> simp only [hb, Bool.false_eq_true, if_false, if_true, Nat.mul_zero, Nat.zero_add] at hstep <;> omega
      simp only [comparisonValue, comparisonRhs, if_pos hp, hv, List.replicate_one,
        List.flatMap_singleton, comparisonInterpret_inl]
    · have hkpos : 0 < k := by
        by_cases he : k = 0
        · exact False.elim (hp (by rw [he, prefixValue_zero]))
        · omega
      have he : k-1+1 = k := by omega
      change List.replicate (prefixValue (chunk h D s) (k+1)) 0 = _
      rw [unary_prefix_expansion _ _ hk]
      cases hb : ((chunk h D s)[k]?).getD false <;>
        simp only [comparisonRhs, if_neg hp, hb, Bool.false_eq_true, if_false, if_true,
          List.flatMap_append, List.flatMap_replicate, comparisonInterpret_inr, comparisonValue,
          he, List.flatMap_nil, List.flatMap_singleton, comparisonInterpret_inl]
  | power j =>
    cases j with
    | zero =>
      simp only [comparisonValue, comparisonRhs, Nat.zero_add, ite_true,
        List.flatMap_replicate, comparisonInterpret_inl, List.flatten_replicate_singleton, Nat.pow_one]
    | succ j =>
      have hj : j+1 ≠ 0 := by omega
      simp only [comparisonValue, comparisonRhs, if_neg hj, Nat.add_sub_cancel,
        List.flatMap_replicate, comparisonInterpret_inr, List.flatten_replicate_replicate]
      rw [Nat.pow_succ 64 (j+1), Nat.mul_comm]
  | aux j u c =>
    cases u with
    | zero =>
      simp [comparisonValue, comparisonRhs, comparisonInterpret, comparisonAuxValue_zero, comparisonInterpret_inl, comparisonInterpret_inr]
    | succ u =>
      simp only [comparisonValue, comparisonRhs, List.flatMap_map, comparisonAuxValue_succ,
        Function.comp_def, comparisonInterpret_inr, comparisonValue]
  | start => exact (comparisonStartRhs_expansion h D hh).symm

/-- The actual finite comparison grammar, including all positive prefix
rules, all unary powers, all morphism layers, and the full start production. -/
noncomputable def comparisonRecipe (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) : GrammarRecipe ComparisonIndex (inputStart h D) where
  defined := (comparisonIndices h D).toFinset
  rhs := comparisonRhs h D
  value := comparisonValue h D
  start := start
  start_mem := List.mem_toFinset.mpr ((mem_comparisonIndices h D start).mpr trivial)
  rank := comparisonRank h
  nonempty := fun x _ => comparisonRhs_nonempty h D x
  terminal_bound := fun x hx a ha => comparisonRhs_terminal_bound h D x
    ((mem_comparisonIndices h D x).mp (List.mem_toFinset.mp hx)) a ha
  reference := by
    intro x hx y hy
    have hv := comparisonRhs_reference h D hh hD x
      ((mem_comparisonIndices h D x).mp (List.mem_toFinset.mp hx)) y hy
    exact ⟨List.mem_toFinset.mpr ((mem_comparisonIndices h D y).mpr hv.1), hv.2⟩
  equation := fun x hx => comparisonRhs_equation h D hh hD x
    ((mem_comparisonIndices h D x).mp (List.mem_toFinset.mp hx))

noncomputable def comparisonGrammar (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) : Grammar := (comparisonRecipe h D hh hD).compile ComparisonIndex.code

theorem comparisonGrammar_wellFormed (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) : (comparisonGrammar h D hh hD).WellFormed :=
  (comparisonRecipe h D hh hD).compile_wellFormed _ ComparisonIndex.code_injective

theorem comparisonGrammar_generates (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) : (comparisonGrammar h D hh hD).Generates (inputWord h D) :=
  (comparisonRecipe h D hh hD).compile_generates _ ComparisonIndex.code_injective

end GreedyLowerBound
