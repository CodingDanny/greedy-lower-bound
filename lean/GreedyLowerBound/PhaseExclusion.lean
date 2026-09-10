import GreedyLowerBound.PhaseStorage

set_option autoImplicit false

namespace GreedyLowerBound

theorem UsesOnePrimary.absent_private {κ : Type} {owner : Nat → Option κ}
    {C D : κ} {X a : Nat} {w : Word Nat} (hw : UsesOnePrimary owner C X w)
    (hX : owner X = none) (ha : owner a = some D) (hCD : C ≠ D) : a ∉ w := by
  intro hm
  rcases hw a hm with he | he
  · rw [he, hX] at ha
    contradiction
  · exact hCD (Option.some.inj (he.symm.trans ha))

namespace PhaseStorage

theorem unfinished_alphabet {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (s : Nat) (hs : s < h-t) :
    UsesOnePrimary S.owner (Sum.inl (t+s)) (S.primary t)
      (paddedRuns (S.primary t) (64^(s+1)) (auxiliaryMarkers h (t+s))) := by
  apply UsesOnePrimary.padded
  intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  exact S.marker_owned (t+s) (by omega) c

theorem marker_absent_target {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (j : Nat) (hj : j < h) (c : Letter) (n : Nat) :
    markerName j c ∉ targetState n S.primary t := by
  intro hm
  obtain ⟨i, hi, he⟩ := targetState_mem n S.primary t (markerName j c) hm
  have ho := S.marker_owned j hj c
  rw [he, S.primary_unowned i hi] at ho
  contradiction

theorem unfinished_marker_absent_cleanup {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (j : Nat) (hjt : t ≤ j) (hj : j < h) (c : Letter)
    (w : Word Nat) (hw : w ∈ S.finished.map Prod.snd ++ S.powers.map Prod.snd) :
    markerName j c ∉ w := by
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    have hi := S.finished_indices p hp
    exact (S.finished_alphabet p hp).absent_private
      (S.primary_unowned (p.1+1) (by omega)) (S.marker_owned j hj c)
      (by intro he; have he' := Sum.inl.inj he; omega)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    have hi := S.power_indices p hp
    exact (S.power_alphabet p hp).absent_private (S.primary_unowned p.1 (by omega))
      (S.marker_owned j hj c) (by simp)

/-- Exact global count of a factor containing a marker of an unfinished
auxiliary. No future preservation property is assumed in this lemma. -/
theorem marker_frequency {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (s : Nat) (hs : s < h-t) (c : Letter)
    (v : Word Nat) (hv : G.Eligible v) (ha : markerName (t+s) c ∈ v) :
    G.frequency v = scanCount v
      (paddedRuns (S.primary t) (64^(s+1)) (auxiliaryMarkers h (t+s))) := by
  rw [S.partition.frequency_eq v hv, (S.cells.map (scanCount v)).sum_eq]
  change cellFrequency (_ ++ _ ++ _ ++ _) v = _
  rw [cellFrequency_append, cellFrequency_append, cellFrequency_append]
  have htargets : cellFrequency
      ((targetNumbers h D).map (fun n => targetState n S.primary t)) v = 0 := by
    apply cellFrequency_zero_of_missing _ v (markerName (t+s) c) ha
    intro w hw
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hw
    exact S.marker_absent_target (t+s) (by omega) c n
  have hfin : cellFrequency (S.finished.map Prod.snd) v = 0 := by
    apply cellFrequency_zero_of_missing _ v (markerName (t+s) c) ha
    intro w hw
    exact S.unfinished_marker_absent_cleanup (t+s) (by omega) (by omega) c w
      (List.mem_append_left _ hw)
  have hpow : cellFrequency (S.powers.map Prod.snd) v = 0 := by
    apply cellFrequency_zero_of_missing _ v (markerName (t+s) c) ha
    intro w hw
    exact S.unfinished_marker_absent_cleanup (t+s) (by omega) (by omega) c w
      (List.mem_append_right _ hw)
  rw [htargets, hfin, hpow, Nat.zero_add, Nat.add_zero, Nat.add_zero]
  unfold cellFrequency unfinishedCells
  rw [List.map_map, sum_map_range_eq]
  apply Finset.sum_eq_single s
  · intro r hr hrs
    have hr' := Finset.mem_range.mp hr
    apply scanCount_zero_of_missing _ _ (markerName (t+s) c) ha
    exact (S.unfinished_alphabet r hr').absent_private
      (S.primary_unowned t (Nat.le_refl _)) (S.marker_owned (t+s) (by omega) c)
      (by intro he; have he' := Sum.inl.inj he; omega)
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr hs))

theorem marker_loses {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (s : Nat) (hs : s < h-t) (c : Letter)
    (v : Word Nat) (hv : G.Eligible v) (ha : markerName (t+s) c ∈ v) :
    G.gain v < G.gain (List.replicate 64 (S.primary t)) := by
  let f := auxiliaryAlphabet (S.primary t) (t+s)
  let word := paddedRuns (S.primary t) (64^(s+1)) (auxiliaryMarkers h (t+s))
  have hf : Function.Injective f := auxiliaryAlphabet_injective _ _
    (fun c => Ne.symm (S.active_ne_marker (t+s) (by omega) c))
  have hword : (auxiliaryWord (64*64^s) (muIterate (auxiliaryExponent h ((t+s)+1)))).map f =
      word := by
    rw [auxiliaryWord_renamed]
    have hp : 64*64^s = 64^(s+1) := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hp]
    rfl
  have hvn : v ≠ [] := by intro he; have hh := hv.1; simp [he] at hh
  have hfreq : G.frequency v = scanCount v word := S.marker_frequency s hs c v hv ha
  have hp : Packing v word (G.frequency v) := by
    rw [hfreq]
    exact (scanCount_is_maximum v word hvn).1
  have hl := GreedyLowerBound.auxiliary_marker_loses h ((t+s)+1) (64^s)
    (by omega) (by omega) (Nat.one_le_pow _ _ (by decide)) f hf v (G.frequency v)
    (by rw [hword]; exact hp) hv.2
    ⟨markerName (t+s) c, ha, S.active_ne_marker (t+s) (by omega) c⟩
  have hmem : word ∈ S.partition.pieces := S.cells.mem_iff.mpr (by
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩)
  have hB := S.partition.scanCount_le_frequency (List.replicate 64 (S.primary t)) word (by simp) hmem
  have hmarkers := S.active_ne_markers (t+s) (by omega)
  rw [show word = paddedRuns (S.primary t) (64^(s+1)) (auxiliaryMarkers h (t+s)) from rfl,
    scanCount_paddedRuns (S.primary t) 64 (64^(s+1)) _ (by decide) hmarkers,
    auxiliaryMarkers_length] at hB
  have hdiv : 64^(s+1)/64 = 64^s := by rw [Nat.pow_succ, Nat.mul_comm, Nat.mul_div_right _ (by decide : 0 < 64)]
  rw [hdiv] at hB
  have hg := G.gain_mono_frequency (List.replicate 64 (S.primary t))
    (auxiliaryLength h ((t+s)+1)*64^s) (by simp) hB
  simp only [List.length_replicate] at hg
  exact hl.trans_le hg

theorem unfinished_loses {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (hD : D.length = h^2) (s : Nat) (hs : s < h-t)
    (v : Word Nat) (hv : G.Eligible v) (hne : v ≠ List.replicate 64 (S.primary t))
    (hc : 0 < scanCount v (paddedRuns (S.primary t) (64^(s+1)) (auxiliaryMarkers h (t+s)))) :
    G.gain v < G.gain (List.replicate 64 (S.primary t)) := by
  by_cases hall : ∀ a ∈ v, a = S.primary t
  · have he : v = List.replicate v.length (S.primary t) := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
    have hd : v.length ≠ 64 := by intro hd; exact hne (by simpa [hd] using he)
    have hv' : G.Eligible (List.replicate v.length (S.primary t)) := by rw [← he]; exact hv
    have hl := S.unary_loses (by omega) hD v.length hd hv'
    rw [← he] at hl
    exact hl
  · have hex : ∃ a ∈ v, a ≠ S.primary t := by
      by_contra hn
      apply hall
      intro a ha
      by_contra hne
      exact hn ⟨a, ha, hne⟩
    obtain ⟨a, ha, hax⟩ := hex
    have hvn : v ≠ [] := by intro he; have hh := hv.1; simp [he] at hh
    have hin := (scanCount_is_maximum v _ hvn).1.factor_isInfix hc
    have ham := hin.subset ha
    obtain ⟨z, hz, ham⟩ := List.mem_flatMap.mp ham
    rcases List.mem_append.mp ham with ham | ham
    · exact False.elim (hax (List.mem_replicate.mp ham).2)
    · have he : a = z := by simpa using ham
      obtain ⟨c, hc, hz⟩ := List.mem_map.mp hz
      have he' : a = markerName (t+s) c := he.trans hz.symm
      exact S.marker_loses s hs c v hv (he' ▸ ha)

/-- Sections 4.2–4.4 combined: any maximizing choice other than the intended
power has zero occurrences in every target and unfinished auxiliary cell. -/
theorem protected_untouched {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (ht : t < h) (hD : D.length = h^2)
    (v : Word Nat) (hv : G.Eligible v) (hne : v ≠ List.replicate 64 (S.primary t))
    (hmax : ∀ u, G.Eligible u → G.gain u ≤ G.gain v) :
    ∀ w ∈ (S.active ht).protectedCells, scanCount v w = 0 := by
  have hbench : G.Eligible (List.replicate 64 (S.primary t)) := by
    apply (S.active ht).benchmark_eligible
    rw [S.active_current_length ht]
    have hh := auxiliaryLength_gt_mass h (t+1) (by omega) (by omega)
    omega
  have hle := hmax _ hbench
  have he : (S.active ht).protectedCells =
      (targetNumbers h D).map (fun n => targetState n S.primary t) ++
        unfinishedCells h t S.primary := by
    rw [S.unfinished_split ht]
    simp only [ActiveStorage.protectedCells, active, List.map_map,
      Function.comp_def, List.append_assoc, List.singleton_append]
  rw [he]
  intro w hw
  by_contra hn
  have hc : 0 < scanCount v w := by omega
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨n, hnmem, rfl⟩ := List.mem_map.mp hw
    have hl := S.target_loses ht hD n hnmem v hv hne hc
    omega
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hw
    have hl := S.unfinished_loses hD s (List.mem_range.mp hs) v hv hne hc
    omega

end PhaseStorage

end GreedyLowerBound
