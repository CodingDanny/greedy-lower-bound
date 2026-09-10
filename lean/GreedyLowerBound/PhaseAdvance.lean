import GreedyLowerBound.PrimaryAdvance

set_option autoImplicit false

namespace GreedyLowerBound.PhaseStorage

/-- Section 4.6: the actual prescribed global substitution advances the
entire literal class invariant, including both newly assigned storage cells.
The new primary's definition belongs to the new power layer; the current
auxiliary becomes a finished auxiliary. -/
noncomputable def advance {G H : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (ht : t < h) (hD : D.length = h^2)
    {fresh : Nat} {counts : Nat → Nat}
    (hr : GlobalStep G H (List.replicate 64 (S.primary t)) fresh counts) :
    PhaseStorage H h D (t+1) := by
  let v := List.replicate 64 (S.primary t)
  have hvn : v ≠ [] := by simp [v]
  have hv : G.Eligible v := by
    apply (S.active ht).benchmark_eligible
    rw [S.active_current_length ht]
    have hh := auxiliaryLength_gt_mass h (t+1) (by omega) (by omega)
    omega
  let A := advancePrimaries S.primary t fresh
  let own := unsetOwner S.owner fresh
  let doneWord := paddedRuns fresh 1 (auxiliaryMarkers h t)
  have hfr : ∀ i ≤ t, fresh ≠ S.primary i := S.fresh_ne_primary (by omega) hD hr hvn
  have hA : ∀ i ≤ t, A i = S.primary i :=
    advancePrimaries_old S.primary S.primary_injective t fresh hfr
  have hAn : A (t+1) = fresh := advancePrimaries_new S.primary t fresh
  have hmarkers : ∀ z ∈ auxiliaryMarkers h t, z ≠ fresh := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
    exact Ne.symm (S.fresh_ne_marker hr hvn t ht c)
  have hfinmem : ∀ p ∈ S.finished, p.2 ∈ S.partition.pieces := by
    intro p hp
    apply S.cells.mem_iff.mpr
    apply List.mem_append_left
    exact List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hpowmem : ∀ p ∈ S.powers, p.2 ∈ S.partition.pieces := by
    intro p hp
    exact S.cells.mem_iff.mpr (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  refine {
    wellFormed := hr.wellFormed S.wellFormed hvn
    generates := hr.preserves_word _ S.generates
    partition := S.partition.afterStep hr hv
    primary := A
    primary_zero := (hA 0 (by omega)).trans S.primary_zero
    primary_injective := advancePrimaries_injective S.primary S.primary_injective t fresh
    primary_defined := ?_
    primary_not_start := ?_
    target_first := ?_
    target_rest := ?_
    owner := own
    primary_unowned := ?_
    marker_owned := ?_
    finished := S.finished ++ [(t,doneWord)]
    powers := S.powers ++ [(t,v)]
    finished_indices := ?_
    power_indices := ?_
    finished_alphabet := ?_
    power_alphabet := ?_
    finished_noAdjacent := ?_
    cells := ?_ }
  · intro i hi hit
    rw [hr.domain]
    by_cases he : i = t+1
    · rw [he, hAn]
      exact Finset.mem_insert_self _ _
    · rw [hA i (by omega)]
      exact Finset.mem_insert_of_mem (S.primary_defined i hi (by omega))
  · intro i hi
    rw [hr.start]
    by_cases he : i = t+1
    · rw [he, hAn]
      exact hr.fresh_start
    · rw [hA i (by omega)]
      exact S.primary_not_start i (by omega)
  · rw [Fragmentation.afterStep_first, S.target_first]
    exact scanOutput_target_advance _ S.primary S.primary_injective t fresh hfr
  · have he : (((S.partition.afterStep hr hv).rest).map Prod.snd).take
        ((targetNumbers h D).length-1) =
        ((S.partition.rest.map Prod.snd).take ((targetNumbers h D).length-1)).map (scanOutput v fresh) := by
      simp only [Fragmentation.afterStep_rest, List.map_map, List.map_take, Function.comp_def, v]
    rw [he, S.target_rest, List.map_map]
    apply List.map_congr_left
    intro n hn
    exact scanOutput_target_advance n S.primary S.primary_injective t fresh hfr
  · intro i hi
    by_cases he : i = t+1
    · simp only [he, hAn, own, unsetOwner, if_pos rfl, if_true]
    · rw [hA i (by omega)]
      simp only [own, unsetOwner, if_neg (Ne.symm (hfr i (by omega))),
        S.primary_unowned i (by omega)]
  · intro j hj c
    have hf := S.fresh_ne_marker hr hvn j hj c
    simp only [own, unsetOwner, if_neg (Ne.symm hf), S.marker_owned j hj c]
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · have hh := S.finished_indices p hp
      omega
    · have he : p = (t,doneWord) := by simpa using hp
      simp [he]
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · have hh := S.power_indices p hp
      omega
    · have he : p = (t,v) := by simpa using hp
      simp [he]
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · have hi := S.finished_indices p hp
      rw [hA (p.1+1) (by omega)]
      exact (S.finished_alphabet p hp).unset (S.partition.fresh_absent_cell hr _ (hfinmem p hp))
    · have he : p = (t,doneWord) := by simpa using hp
      subst p
      simp only [hAn]
      apply UsesOnePrimary.padded
      intro a ha
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
      have hf := S.fresh_ne_marker hr hvn t ht c
      simp only [own, unsetOwner, if_neg (Ne.symm hf), S.marker_owned t ht c]
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · have hi := S.power_indices p hp
      rw [hA p.1 (by omega)]
      exact (S.power_alphabet p hp).unset (S.partition.fresh_absent_cell hr _ (hpowmem p hp))
    · have he : p = (t,v) := by simpa using hp
      subst p
      intro a ha
      exact Or.inl ((List.mem_replicate.mp ha).2.trans (hA t (Nat.le_refl _)).symm)
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · have hi := S.finished_indices p hp
      rw [hA (p.1+1) (by omega)]
      exact S.finished_noAdjacent p hp
    · have he : p = (t,doneWord) := by simpa using hp
      subst p
      simp only [hAn]
      exact paddedRuns_one_noAdjacent fresh _ hmarkers
  · let targets := (targetNumbers h D).map (fun n => targetState n A (t+1))
    let remaining := unfinishedCells h (t+1) A
    have htargets : ((targetNumbers h D).map (fun n => targetState n S.primary t)).map
        (scanOutput v fresh) = targets := by
      rw [List.map_map]
      apply List.map_congr_left
      intro n hn
      exact scanOutput_target_advance n S.primary S.primary_injective t fresh hfr
    have hremaining : (unfinishedCells h t S.primary).map (scanOutput v fresh) =
        doneWord :: remaining := by
      rw [S.scanned_unfinished ht fresh]
      simp only [remaining, unfinishedCells, hAn]
      rfl
    have hfin : (S.finished.map Prod.snd).map (scanOutput v fresh) = S.finished.map Prod.snd := by
      rw [List.map_map]
      apply List.map_congr_left
      intro p hp
      exact S.scanned_cleanup fresh p.2 (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
    have hpow : (S.powers.map Prod.snd).map (scanOutput v fresh) = S.powers.map Prod.snd := by
      rw [List.map_map]
      apply List.map_congr_left
      intro p hp
      exact S.scanned_cleanup fresh p.2 (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
    have hp := (S.partition.afterStep_pieces hr hv).trans
      ((S.cells.map (scanOutput v fresh)).append_right [v])
    rw [List.map_append, List.map_append, List.map_append, htargets, hremaining, hfin, hpow] at hp
    apply hp.trans
    change (targets ++ doneWord :: remaining ++ S.finished.map Prod.snd ++ S.powers.map Prod.snd ++ [v]).Perm
      (targets ++ remaining ++ (S.finished ++ [(t,doneWord)]).map Prod.snd ++
        (S.powers ++ [(t,v)]).map Prod.snd)
    simp only [List.map_append, List.map_cons, List.map_nil]
    have hh := (List.perm_middle (a := doneWord)
      (l₁ := remaining ++ S.finished.map Prod.snd) (l₂ := S.powers.map Prod.snd ++ [v])).symm.append_left targets
    simpa only [List.append_assoc, List.cons_append, List.singleton_append] using hh

end GreedyLowerBound.PhaseStorage
