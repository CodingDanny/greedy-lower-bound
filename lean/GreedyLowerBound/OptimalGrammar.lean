import GreedyLowerBound.InitialGrammar
import GreedyLowerBound.TerminalSymbols
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
namespace GreedyLowerBound
namespace Grammar

def HasSize (w : Word Nat) (n : Nat) : Prop :=
  ∃ G : Grammar, G.WellFormed ∧ G.Generates w ∧ G.size = n

/-- The minimum literal grammar size. The zero convention for words with no
well-formed grammar is irrelevant to the proved nonempty-input theorems. -/
noncomputable def minimumSize (w : Word Nat) : Nat := by
  classical
  exact if h : ∃ n, HasSize w n then Nat.find h else 0

theorem hasSize_exists (w : Word Nat) (hw : w ≠ []) : ∃ n, HasSize w n := by
  let start := w.toFinset.sup id + 1
  have hs : start ∉ w := by
    intro hm
    have hl : start ≤ w.toFinset.sup id := Finset.le_sup (f := id) (List.mem_toFinset.mpr hm)
    dsimp [start] at hl
    omega
  exact ⟨w.length, initial w start, initial_wellFormed w start hw hs,
    initial_generates w start hs, initial_size w start⟩

theorem minimumSize_attained (w : Word Nat) (hw : w ≠ []) :
    ∃ G : Grammar, G.WellFormed ∧ G.Generates w ∧ G.size = minimumSize w := by
  classical
  have hex := hasSize_exists w hw
  simpa only [minimumSize, dif_pos hex] using Nat.find_spec hex

theorem minimumSize_le (G : Grammar) (hG : G.WellFormed) (w : Word Nat)
    (hw : G.Generates w) : minimumSize w ≤ G.size := by
  classical
  have hex : ∃ n, HasSize w n := ⟨G.size, G, hG, hw, rfl⟩
  simpa only [minimumSize, dif_pos hex] using Nat.find_min' hex ⟨G, hG, hw, rfl⟩

theorem minimumSize_pos (w : Word Nat) (hw : w ≠ []) : 0 < minimumSize w := by
  obtain ⟨G, hG, _, he⟩ := minimumSize_attained w hw
  have hc : 0 < G.defined.card := Finset.card_pos.mpr ⟨G.start, hG.1⟩
  have hs := G.card_le_size hG
  omega

/-- A generated terminal must occur literally in some production. -/
theorem generated_symbol_in_rhs (G : Grammar) (hG : G.WellFormed)
    (w : Word Nat) (hw : G.Generates w) (a : Nat) (ha : a ∈ w) :
    ∃ i ∈ G.defined, a ∈ G.rhs i := by
  obtain ⟨value, hv, he⟩ := hw
  obtain ⟨rank, hr⟩ := hG.2.2
  have aux : ∀ n i, rank i = n → i ∈ G.defined → a ∈ value i →
      ∃ j ∈ G.defined, a ∈ G.rhs j := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro i hi hid ha
      rw [hv.1 i hid] at ha
      obtain ⟨j, hj, ha⟩ := List.mem_flatMap.mp ha
      by_cases hjd : j ∈ G.defined
      · exact ih (rank j) (by have := hr i hid j hjd hj; omega) j rfl hjd ha
      · rw [hv.2 j hjd] at ha
        have he : a = j := by simpa using ha
        exact ⟨i, hid, he ▸ hj⟩
  exact aux (rank G.start) G.start rfl hG.1 (he ▸ ha)

/-- Alphabet size is a lower bound for every grammar under the literal RHS
length convention, including grammars with unreachable rules. -/
theorem alphabet_card_le_size (G : Grammar) (hG : G.WellFormed)
    (w : Word Nat) (hw : G.Generates w) : w.toFinset.card ≤ G.size := by
  have hsub : w.toFinset ⊆ G.defined.biUnion (fun i => (G.rhs i).toFinset) := by
    intro a ha
    obtain ⟨i, hi, hm⟩ := G.generated_symbol_in_rhs hG w hw a (List.mem_toFinset.mp ha)
    exact Finset.mem_biUnion.mpr ⟨i, hi, List.mem_toFinset.mpr hm⟩
  calc
    _ ≤ (G.defined.biUnion (fun i => (G.rhs i).toFinset)).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ G.defined, (G.rhs i).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ G.defined, (G.rhs i).length :=
      Finset.sum_le_sum (fun i _ => List.toFinset_card_le _)
    _ = G.size := rfl

theorem alphabet_card_le_minimumSize (w : Word Nat) (hw : w ≠ []) :
    w.toFinset.card ≤ minimumSize w := by
  obtain ⟨G, hG, hg, he⟩ := minimumSize_attained w hw
  rw [← he]
  exact G.alphabet_card_le_size hG w hg

end Grammar
end GreedyLowerBound
