import GreedyLowerBound.Grammar
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false

namespace GreedyLowerBound

variable {G H : Grammar} {v : Word Nat} {fresh : Nat} {counts : Nat → Nat}

theorem GlobalStep.wellFormed (h : GlobalStep G H v fresh counts)
    (hG : G.WellFormed) (hv : v ≠ []) : H.WellFormed := by
  rcases hG with ⟨hs, hne, rank, hr⟩
  let deps := G.defined.filter (fun j => j ∈ v)
  let height := deps.sup (fun j => rank j + 1)
  let nextRank := fun j => if j = fresh then 2 * height else 2 * rank j + 1
  have dep_le : ∀ j ∈ G.defined, j ∈ v → rank j + 1 ≤ height := by
    intro j hj hjv
    exact Finset.le_sup (s := deps) (f := fun j => rank j + 1)
      (Finset.mem_filter.mpr ⟨hj, hjv⟩)
  have height_le : ∀ i ∈ G.defined, 0 < counts i → height ≤ rank i := by
    intro i hi hc
    apply Finset.sup_le
    intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjd, hjv⟩
    have hjin := (h.scans i hi).factor_mem_of_positive hc j hjv
    exact hr i hi j hjd hjin
  refine ⟨?_, ?_, nextRank, ?_⟩
  · rw [h.start, h.domain]
    exact Finset.mem_insert_of_mem hs
  · intro i hi
    rw [h.domain] at hi
    rcases Finset.mem_insert.mp hi with he | hi
    · simpa only [he, h.new_rule] using hv
    · exact (h.scans i hi).nonempty_output (hne i hi)
  · intro i hi j hj hm
    rw [h.domain] at hi hj
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      rw [h.new_rule] at hm
      have hjne : j ≠ fresh := by intro he; subst j; exact h.fresh_factor hm
      have hjold := (Finset.mem_insert.mp hj).resolve_left hjne
      have hle := dep_le j hjold hm
      simp only [nextRank, if_pos rfl, if_neg hjne]
      omega
    · have hine : i ≠ fresh := by intro he; subst i; exact h.fresh_defined hi
      rcases Finset.mem_insert.mp hj with hj | hj
      · subst j
        have hc : 0 < counts i := by
          by_contra hn
          have hz : counts i = 0 := by omega
          have he := (h.scans i hi).zero_eq hz
          rw [← he] at hm
          exact h.fresh_rhs i hi hm
        have hle := height_le i hi hc
        simp only [nextRank, if_pos rfl, if_neg hine]
        omega
      · have hjne : j ≠ fresh := by intro he; subst j; exact h.fresh_defined hj
        have hmem := ((h.scans i hi).output_mem j hm).resolve_left hjne
        have hlt := hr i hi j hj hmem
        simp only [nextRank, if_neg hine, if_neg hjne]
        omega

end GreedyLowerBound
