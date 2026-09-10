import GreedyLowerBound.Greedy
import GreedyLowerBound.GrammarSemantics

set_option autoImplicit false

namespace GreedyLowerBound

theorem GreedyStep.defined_subset {G H : Grammar} (h : GreedyStep G H) :
    G.defined ⊆ H.defined := by
  rcases h with ⟨v, fresh, hr, _, _⟩
  rw [hr.domain]
  exact Finset.subset_insert _ _

theorem GreedyRun.start_eq {G H : Grammar} {n : Nat} (h : GreedyRun G H n) :
    H.start = G.start := by
  induction h with
  | nil => rfl
  | cons hs ht ih =>
    obtain ⟨v, fresh, hr, _, _⟩ := hs
    exact ih.trans hr.start

/-- The interpretation frozen immediately after the primary phases survives
an arbitrary number of subsequent Greedy rounds. -/
theorem GreedyRun.preserves_frozen_word {G H : Grammar} {n : Nat}
    (h : GreedyRun G H n) (F : Finset Nat) (hF : F ⊆ G.defined)
    (w : Word Nat) (hw : (G.freeze F).Generates w) : (H.freeze F).Generates w := by
  induction h with
  | nil => exact hw
  | @cons G H K n hs ht ih =>
    have hFH : F ⊆ H.defined := Finset.Subset.trans hF hs.defined_subset
    apply ih hFH
    rcases hs with ⟨v, fresh, hr, _, _⟩
    have hf : fresh ∉ F := by intro hm; exact hr.fresh_defined (hF hm)
    exact hr.preserves_frozen_word hf w hw

/-- The frozen grammar after all later rounds has the same frozen word and
size at most the actual final grammar. This is the semantic core of Section 5;
separator truncation and terminal erasure are separate obligations. -/
theorem GreedyRun.frozen_final_grammar {G H : Grammar} {n : Nat}
    (h : GreedyRun G H n) (hG : G.WellFormed) (F : Finset Nat)
    (hF : F ⊆ G.defined) (hs : H.start ∉ F)
    (w : Word Nat) (hw : (G.freeze F).Generates w) :
    (H.freeze F).WellFormed ∧ (H.freeze F).Generates w ∧ (H.freeze F).size ≤ H.size := by
  exact ⟨Grammar.freeze_wellFormed (h.wellFormed hG) hs,
    h.preserves_frozen_word F hF w hw, H.freeze_size_le F⟩

end GreedyLowerBound
