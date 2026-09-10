import GreedyLowerBound.InputAssembly

set_option autoImplicit false

namespace GreedyLowerBound

def auxiliaryMarkers (h j : Nat) : Word Nat :=
  (muIterate (auxiliaryExponent h (j+1))).map (markerName j)

theorem auxiliaryMarkers_length (h j : Nat) :
    (auxiliaryMarkers h j).length = auxiliaryLength h (j+1) := by
  simp [auxiliaryMarkers, muIterate_length, auxiliaryLength]

theorem auxiliaryMarkers_nonzero (h j : Nat) (z : Nat) (hz : z ∈ auxiliaryMarkers h j) :
    z ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
  simp [markerName]

theorem inputAuxiliary_padded (h j : Nat) :
    inputAuxiliary h j = paddedRuns 0 (64^(j+1)) (auxiliaryMarkers h j) := by
  exact auxiliaryWord_renamed _ _ _

/-- Phase 1's exhaustive active-storage model, instantiated by the actual
input grammar. No hypothesis about Greedy's future behavior is assumed. -/
noncomputable def initialActiveStorage (h : Nat) (D : List Bool) (hh : 1 ≤ h) :
    ActiveStorage (inputGrammar h D) 0 where
  partition := inputPartition h D
  targets := (targetNumbers h D).map (fun n => List.replicate n 0)
  current := auxiliaryMarkers h 0
  later := (List.range (h-1)).map (fun j => (64^(j+1), auxiliaryMarkers h (j+1)))
  cleanup := []
  current_markers := auxiliaryMarkers_nonzero h 0
  later_markers := by
    intro p hp z hz
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    exact auxiliaryMarkers_nonzero h (j+1) z hz
  cleanup_noAdjacent := by simp
  cells := by
    rw [inputPartition_pieces h D hh]
    have he : h = (h-1)+1 := by omega
    have hrange : List.range h = 0 :: (List.range (h-1)).map Nat.succ := by
      conv_lhs => rw [he]
      exact List.range_succ_eq_map
    rw [hrange]
    simp only [List.map_cons, List.map_map, List.append_nil]
    apply List.Perm.of_eq
    rw [List.append_assoc, List.singleton_append]
    apply congrArg (List.append ((targetNumbers h D).map (fun n => List.replicate n 0)))
    congr 1
    · simpa only [Nat.zero_add, Nat.pow_one] using inputAuxiliary_padded h 0
    · apply List.map_congr_left
      intro j hj
      simp only [Function.comp_def]
      rw [inputAuxiliary_padded]
      have hp : 64^(j+1+1) = 64*64^(j+1) := by rw [Nat.pow_succ, Nat.mul_comm]
      exact congrArg (fun L => paddedRuns 0 L (auxiliaryMarkers h (j+1))) hp

theorem initialActiveStorage_target_mass (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) : cellMass (initialActiveStorage h D hh).targets ≤ targetMass h := by
  have he : cellMass (initialActiveStorage h D hh).targets = (targetNumbers h D).sum := by
    simp [cellMass, initialActiveStorage, List.map_map, Function.comp_def]
  rw [he]
  exact targetNumbers_sum_le h D hD

theorem initialActiveStorage_current_length (h : Nat) (D : List Bool) (hh : 1 ≤ h) :
    (initialActiveStorage h D hh).current.length = auxiliaryLength h 1 :=
  auxiliaryMarkers_length h 0

theorem sum_map_range_eq (f : Nat → Nat) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem initialActiveStorage_later_mass (h : Nat) (D : List Bool) (hh : 1 ≤ h) :
    (initialActiveStorage h D hh).laterMass = laterAuxiliaryMass h 1 := by
  unfold ActiveStorage.laterMass
  change (((List.range (h-1)).map (fun j =>
    (64^(j+1), auxiliaryMarkers h (j+1)))).map (fun p => p.2.length*(64*p.1))).sum = _
  rw [List.map_map, sum_map_range_eq]
  unfold laterAuxiliaryMass
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Function.comp_def, auxiliaryMarkers_length, phaseWeight]
  have hi : 1+(j+1) = j+1+1 := by omega
  rw [hi]
  simp only [Nat.pow_succ]
  ac_rfl

/-- Actual phase-1 eligibility and strict global exclusion of every competing
active unary length, before any cleanup. -/
theorem inputGrammar_unary_loses (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) (d : Nat) (hd : d ≠ 64)
    (hv : (inputGrammar h D).Eligible (List.replicate d 0)) :
    (inputGrammar h D).gain (List.replicate d 0) <
      (inputGrammar h D).gain (List.replicate 64 0) := by
  apply (initialActiveStorage h D hh).unary_loses (targetMass h) d
    (initialActiveStorage_target_mass h D hh hD) _ _ hd hv
  · rw [initialActiveStorage_current_length]
    have hg := auxiliaryLength_gt_mass h 1 hh hh
    omega
  · rw [initialActiveStorage_current_length, initialActiveStorage_later_mass]
    exact laterAuxiliaryMass_lt h 1 hh

end GreedyLowerBound
