import GreedyLowerBound.GrammarWellFormed
import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace GreedyLowerBound.Grammar

/-- Acyclicity makes the expansion equations unambiguous. -/
theorem semantics_unique (G : Grammar) (hG : G.WellFormed)
    (value other : Nat → Word Nat) (hv : G.Semantics value) (ho : G.Semantics other) :
    value = other := by
  obtain ⟨_, _, rank, hr⟩ := hG
  have aux : ∀ n : Nat, ∀ i : Nat, rank i = n → value i = other i := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro i hi
      by_cases hid : i ∈ G.defined
      · rw [hv.1 i hid, ho.1 i hid]
        apply List.flatMap_congr
        intro j hj
        by_cases hjd : j ∈ G.defined
        · exact ih (rank j) (by have := hr i hid j hjd hj; omega) j rfl
        · rw [hv.2 j hjd, ho.2 j hjd]
      · rw [hv.2 i hid, ho.2 i hid]
  funext i
  exact aux (rank i) i rfl

theorem generated_word_unique (G : Grammar) (hG : G.WellFormed)
    (w z : Word Nat) (hw : G.Generates w) (hz : G.Generates z) : w = z := by
  obtain ⟨value, hv, hw⟩ := hw
  obtain ⟨other, ho, hz⟩ := hz
  have he := G.semantics_unique hG value other hv ho
  rw [he] at hw
  exact hw.symm.trans hz

end GreedyLowerBound.Grammar
