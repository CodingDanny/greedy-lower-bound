import GreedyLowerBound.Greedy
import GreedyLowerBound.MaximumOccurrences

set_option autoImplicit false

namespace GreedyLowerBound.Grammar

theorem eligible_length_le (G : Grammar) (v : Word Nat) (hv : G.Eligible v) :
    v.length ≤ G.size := by
  have hn : v ≠ [] := by intro he; have hl := hv.1; simp only [he, List.length_nil] at hl; omega
  obtain ⟨i, hi, hc⟩ : ∃ i ∈ G.defined, 0 < scanCount v (G.rhs i) := by
    by_contra hnone
    have heach : ∀ i ∈ G.defined, scanCount v (G.rhs i) = 0 := by
      intro i hi
      by_contra hz
      apply hnone
      exact ⟨i, hi, by omega⟩
    have hzero : G.frequency v = 0 := Finset.sum_eq_zero heach
    have htwo := hv.2
    omega
  obtain ⟨t, ht⟩ := Scan.exists_output v (G.rhs i) 0 hn
  have hlen := ht.factor_length_le hc
  have hsize : (G.rhs i).length ≤ G.size :=
    Finset.single_le_sum (f := fun j => (G.rhs j).length) (fun _ _ => Nat.zero_le _) hi
  exact Nat.le_trans hlen hsize

/-- Every eligible factor is dominated by a maximal factor. Length strictly
increases in the induction, and every eligible length is bounded by grammar size. -/
theorem eligible_dominated_by_maximal (G : Grammar) (v : Word Nat) (hv : G.Eligible v) :
    ∃ u, G.Maximal u ∧ G.gain v ≤ G.gain u := by
  have aux : ∀ k : Nat, ∀ v : Word Nat, G.size-v.length = k → G.Eligible v →
      ∃ u, G.Maximal u ∧ G.gain v ≤ G.gain u := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro v hk hv
      by_cases hm : G.Maximal v
      · exact ⟨v, hm, le_refl _⟩
      obtain ⟨u, hlu, hcu⟩ : ∃ u : Word Nat,
          v.length < u.length ∧ G.frequency v ≤ G.frequency u := by
        by_contra hnone
        apply hm
        refine ⟨hv, ?_⟩
        intro u hu
        by_contra hcount
        apply hnone
        exact ⟨u, hu, by omega⟩
      have he : G.Eligible u := ⟨by have := hv.1; omega, by have := hv.2; omega⟩
      have hbound := G.eligible_length_le u he
      have hlt : G.size-u.length < k := by omega
      obtain ⟨z, hz, hgz⟩ := ih (G.size-u.length) hlt u rfl he
      refine ⟨z, hz, ?_⟩
      exact le_trans (le_of_lt (G.gain_strict_of_longer v u hv hlu hcu)) hgz
  exact aux (G.size-v.length) v rfl hv

/-- Exact equivalence of the two maximization conventions, independent of ties. -/
theorem maximum_iff_maximal_maximum (G : Grammar) (v : Word Nat) :
    (G.Eligible v ∧ ∀ u, G.Eligible u → G.gain u ≤ G.gain v) ↔
    (G.Maximal v ∧ ∀ u, G.Maximal u → G.gain u ≤ G.gain v) := by
  constructor
  · rintro ⟨he, hm⟩
    exact ⟨G.maximizing_is_maximal v he hm, fun u hu => hm u hu.1⟩
  · rintro ⟨he, hm⟩
    refine ⟨he.1, ?_⟩
    intro u hu
    obtain ⟨z, hz, hgz⟩ := G.eligible_dominated_by_maximal u hu
    exact le_trans hgz (hm z hz)

end GreedyLowerBound.Grammar
