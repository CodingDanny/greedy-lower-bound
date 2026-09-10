import GreedyLowerBound.FirstPhase

set_option autoImplicit false

namespace GreedyLowerBound

theorem Grammar.expansion_terminal {G : Grammar} (hG : G.WellFormed)
    (value : Nat → Word Nat) (hvalue : G.Semantics value) (i : Nat) :
    ∀ a ∈ value i, a ∉ G.defined := by
  obtain ⟨rank, hr⟩ := hG.2.2
  generalize he : rank i = n
  induction n using Nat.strongRecOn generalizing i with
  | ind n ih =>
    intro a ha
    by_cases hi : i ∈ G.defined
    · rw [hvalue.1 i hi] at ha
      obtain ⟨j, hj, ha⟩ := List.mem_flatMap.mp ha
      by_cases hjd : j ∈ G.defined
      · exact ih (rank j) (by have hh := hr i hi j hjd hj; omega) j rfl a ha
      · rw [hvalue.2 j hjd] at ha
        have he' : a = j := by simpa using ha
        exact he' ▸ hjd
    · rw [hvalue.2 i hi] at ha
      have he' : a = i := by simpa using ha
      exact he' ▸ hi

theorem Grammar.generated_symbol_terminal {G : Grammar} (hG : G.WellFormed)
    {w : Word Nat} (hw : G.Generates w) (a : Nat) (ha : a ∈ w) : a ∉ G.defined := by
  obtain ⟨value, hv, he⟩ := hw
  rw [← he] at ha
  exact G.expansion_terminal hG value hv G.start a ha

theorem GlobalStep.fresh_ne_input_symbol {G H : Grammar} {v w : Word Nat}
    {fresh : Nat} {counts : Nat → Nat} (hr : GlobalStep G H v fresh counts)
    (hG : G.WellFormed) (hw : G.Generates w) (hv : v ≠ []) (a : Nat) (ha : a ∈ w) :
    fresh ≠ a := by
  intro he
  have ht := Grammar.generated_symbol_terminal (hr.wellFormed hG hv) (hr.preserves_word w hw) a ha
  apply ht
  rw [hr.domain, ← he]
  exact Finset.mem_insert_self _ _

theorem mu_contains_letters : ∀ a c : Letter, c ∈ mu a := by decide

theorem muIterate_contains_letters (e : Nat) (he : 1 ≤ e) (c : Letter) : c ∈ muIterate e := by
  have he' : e = (e-1)+1 := by omega
  rw [he', muIterate]
  have hlen := muIterate_length (e-1)
  have hne : muIterate (e-1) ≠ [] := by
    intro heq
    have hp : 0 < 19^(e-1) := Nat.pow_pos (by decide)
    simp only [heq, List.length_nil] at hlen
    omega
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
  exact List.mem_flatMap.mpr ⟨a, ha, mu_contains_letters a c⟩

theorem inputAuxiliary_contains_marker (h j : Nat) (hj : j < h) (c : Letter) :
    markerName j c ∈ inputAuxiliary h j := by
  have he := auxiliaryExponent_ge h (j+1) (by omega)
  have hc := muIterate_contains_letters (auxiliaryExponent h (j+1)) (by omega) c
  apply List.mem_map.mpr
  refine ⟨some c, ?_, rfl⟩
  exact List.mem_flatMap.mpr ⟨c, hc, by simp⟩

theorem inputWord_contains_marker (h : Nat) (D : List Bool) (j : Nat) (hj : j < h)
    (c : Letter) : markerName j c ∈ inputWord h D := by
  have hw : inputAuxiliary h j ∈ (inputPartition h D).pieces := by
    rw [inputPartition_pieces h D (by omega)]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  obtain ⟨i, hi, hin⟩ := (inputPartition h D).piece_in_rhs (inputAuxiliary h j) hw
  have hi' : i = inputStart h D := by simpa [inputGrammar, Grammar.initial] using hi
  subst i
  have hm := hin.subset (inputAuxiliary_contains_marker h j hj c)
  simpa [inputGrammar, Grammar.initial] using hm

theorem inputWord_contains_zero (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) : 0 ∈ inputWord h D := by
  have hn := inputFirst_nonempty h D hh hD
  have hm : 0 ∈ inputFirst h D := by
    unfold inputFirst at *
    have hp : (targetNumbers h D).headD 0 ≠ 0 := by
      intro he
      exact hn (by rw [he]; rfl)
    exact List.mem_replicate.mpr ⟨hp, rfl⟩
  exact List.mem_append_left _ hm

end GreedyLowerBound
