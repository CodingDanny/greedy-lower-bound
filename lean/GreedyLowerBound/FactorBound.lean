import GreedyLowerBound.GrammarSemantics
import GreedyLowerBound.Slices
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

set_option autoImplicit false

namespace GreedyLowerBound

def distinctFactors (w : Word Nat) (L : Nat) : Finset (Word Nat) :=
  (Finset.range (w.length+1-L)).image (fun p => slice w p L)

namespace Grammar

/-- Candidate factors charged to a right-hand-side boundary and an offset
between 1 and `L-1`. Boundary zero is harmless extra capacity in the bound. -/
def localFactorCandidates (G : Grammar) (value : Nat → Word Nat) (L i : Nat) :
    Finset (Word Nat) :=
  (Finset.range (G.rhs i).length).biUnion fun k =>
    (Finset.range (L-1)).image fun d =>
      slice ((G.rhs i).flatMap value)
        ((((G.rhs i).take k).flatMap value).length - (d+1))
        L

def factorCandidates (G : Grammar) (value : Nat → Word Nat) (L : Nat) :
    Finset (Word Nat) := G.defined.biUnion (G.localFactorCandidates value L)

theorem localFactorCandidates_card_le (G : Grammar) (value : Nat → Word Nat)
    (L i : Nat) : (G.localFactorCandidates value L i).card ≤ (G.rhs i).length*(L-1) := by
  unfold localFactorCandidates
  calc
    _ ≤ ∑ k ∈ Finset.range (G.rhs i).length,
        ((Finset.range (L-1)).image fun d =>
          slice ((G.rhs i).flatMap value)
            ((((G.rhs i).take k).flatMap value).length-(d+1)) L).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Finset.range (G.rhs i).length, (L-1) := by
      apply Finset.sum_le_sum
      intro k _
      exact le_trans Finset.card_image_le (by rw [Finset.card_range])
    _ = _ := by simp

theorem factorCandidates_card_le (G : Grammar) (value : Nat → Word Nat) (L : Nat) :
    (G.factorCandidates value L).card ≤ G.size*(L-1) := by
  unfold factorCandidates
  calc
    _ ≤ ∑ i ∈ G.defined, (G.localFactorCandidates value L i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ i ∈ G.defined, (G.rhs i).length*(L-1) :=
      Finset.sum_le_sum (fun i _ => G.localFactorCandidates_card_le value L i)
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- Descend through a containing child until the factor crosses a boundary.
A terminal cannot contain a factor of length at least two, and ranks strictly
decrease on every nonterminal descent. -/
theorem factor_mem_candidates_of_short_terminals (G : Grammar) (hG : G.WellFormed)
    (value : Nat → Word Nat)
    (hrules : ∀ i ∈ G.defined, value i = (G.rhs i).flatMap value)
    (hterm : ∀ i ∉ G.defined, (value i).length ≤ 1) (L : Nat) (hL : 2 ≤ L) :
    ∀ i p, p+L ≤ (value i).length → slice (value i) p L ∈ G.factorCandidates value L := by
  obtain ⟨_, _, rank, hr⟩ := hG
  have aux : ∀ n : Nat, ∀ i, rank i = n → ∀ p, p+L ≤ (value i).length →
      slice (value i) p L ∈ G.factorCandidates value L := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro i hin p hb
      have hid : i ∈ G.defined := by
        by_contra hn
        have := hterm i hn
        omega
      have hrhs := hrules i hid
      have hb' : p+L ≤ ((G.rhs i).flatMap value).length := by simpa only [← hrhs] using hb
      rcases slice_flatMap_cases (G.rhs i) value p L (by omega) hb' with hin | hcross
      · obtain ⟨j, hj, q, hq, he⟩ := hin
        have hjd : j ∈ G.defined := by
          by_contra hn
          have := hterm j hn
          omega
        have hjrank : rank j < n := by have := hr i hid j hjd hj; omega
        have hm := ih (rank j) hjrank j rfl q hq
        rw [hrhs, he]
        exact hm
      · obtain ⟨k, hk, hleft, hright⟩ := hcross
        let b := (((G.rhs i).take k).flatMap value).length
        let d := b-p-1
        have hd : d < L-1 := by dsimp [d, b]; omega
        have he : b-(d+1) = p := by dsimp [d, b]; omega
        apply Finset.mem_biUnion.mpr
        refine ⟨i, hid, Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk, ?_⟩⟩
        apply Finset.mem_image.mpr
        refine ⟨d, Finset.mem_range.mpr hd, ?_⟩
        change slice ((G.rhs i).flatMap value) (b-(d+1)) L = slice (value i) p L
        rw [he, hrhs]
  intro i p hp
  exact aux (rank i) i rfl p hp

/-- Specialization to ordinary terminal interpretations. -/
theorem factor_mem_candidates (G : Grammar) (hG : G.WellFormed)
    (value : Nat → Word Nat) (hv : G.Semantics value) (L : Nat) (hL : 2 ≤ L) :
    ∀ i p, p+L ≤ (value i).length → slice (value i) p L ∈ G.factorCandidates value L :=
  G.factor_mem_candidates_of_short_terminals hG value hv.1
    (fun i hi => by rw [hv.2 i hi]; simp) L hL

/-- The factor-capacity bound allows erased terminals and empty expansions. -/
theorem interpreted_distinctFactors_card_le (G : Grammar) (hG : G.WellFormed)
    (value : Nat → Word Nat)
    (hrules : ∀ i ∈ G.defined, value i = (G.rhs i).flatMap value)
    (hterm : ∀ i ∉ G.defined, (value i).length ≤ 1) (L : Nat) (hL : 2 ≤ L) :
    (distinctFactors (value G.start) L).card ≤ G.size*(L-1) := by
  have hsub : distinctFactors (value G.start) L ⊆ G.factorCandidates value L := by
    intro v hv
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hv
    have hpr := Finset.mem_range.mp hp
    rw [← he]
    exact G.factor_mem_candidates_of_short_terminals hG value hrules hterm L hL
      G.start p (by omega)
  exact le_trans (Finset.card_le_card hsub) (G.factorCandidates_card_le value L)

/-- The standard SLP factor-count lemma, for the sum-of-right-hand-side-lengths
size convention used in the manuscript. -/
theorem distinctFactors_card_le (G : Grammar) (hG : G.WellFormed)
    (w : Word Nat) (hw : G.Generates w) (L : Nat) (hL : 2 ≤ L) :
    (distinctFactors w L).card ≤ G.size*(L-1) := by
  obtain ⟨value, hv, hw⟩ := hw
  have hsub : distinctFactors w L ⊆ G.factorCandidates value L := by
    intro v hvfactor
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hvfactor
    have hpr := Finset.mem_range.mp hp
    have hbound : p+L ≤ (value G.start).length := by rw [hw]; omega
    rw [← he, ← hw]
    exact G.factor_mem_candidates hG value hv L hL G.start p hbound
  exact le_trans (Finset.card_le_card hsub) (G.factorCandidates_card_le value L)

end Grammar
end GreedyLowerBound
