import GreedyLowerBound.CleanupClassification

set_option autoImplicit false

namespace GreedyLowerBound

theorem Fragmentation.fresh_absent_cell {G H : Grammar} (P : Fragmentation G)
    {v : Word Nat} {fresh : Nat} {counts : Nat → Nat} (hr : GlobalStep G H v fresh counts)
    (w : Word Nat) (hw : w ∈ P.pieces) : fresh ∉ w := by
  obtain ⟨i, hi, hin⟩ := P.piece_in_rhs w hw
  exact fun hm => hr.fresh_rhs i hi (hin.subset hm)

namespace PhaseStorage

noncomputable def scannedTagged (v : Word Nat) (fresh : Nat) (cells : List (Nat × Word Nat)) :
    List (Nat × Word Nat) := cells.map (fun p => (p.1, scanOutput v fresh p.2))

noncomputable def nextFinished {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (v : Word Nat) (fresh : Nat) (C : CleanupChoice S v) :
    List (Nat × Word Nat) := scannedTagged v fresh S.finished ++ match C.cls with
      | Sum.inl j => [(j,v)]
      | Sum.inr _ => []

noncomputable def nextPowers {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (v : Word Nat) (fresh : Nat) (C : CleanupChoice S v) :
    List (Nat × Word Nat) := scannedTagged v fresh S.powers ++ match C.cls with
      | Sum.inl _ => []
      | Sum.inr u => [(u,v)]

/-- Preservation of the complete literal class model through one permitted
cleanup round. `CleanupChoice` is supplied by the proved exhaustive
classification, and guarded-cell nonoccurrence by the exclusion theorem. -/
noncomputable def afterCleanup {G H : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (ht : t < h) (hD : D.length = h^2)
    {v : Word Nat} {fresh : Nat} {counts : Nat → Nat}
    (hr : GlobalStep G H v fresh counts) (hv : G.Eligible v) (C : CleanupChoice S v)
    (hprotected : ∀ w ∈ (S.active ht).protectedCells, scanCount v w = 0) :
    PhaseStorage H h D t := by
  have hvn : v ≠ [] := by intro he; have hh := hv.1; simp [he] at hh
  let nextOwner := extendOwner S.owner fresh C.cls
  have hnew : UsesOnePrimary nextOwner C.cls (classPrimary S.primary C.cls) v :=
    UsesClass.extend_other C.alphabet hr.fresh_factor
  have hfinmem : ∀ p ∈ S.finished, p.2 ∈ S.partition.pieces := by
    intro p hp
    apply S.cells.mem_iff.mpr
    apply List.mem_append_left
    exact List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hpowmem : ∀ p ∈ S.powers, p.2 ∈ S.partition.pieces := by
    intro p hp
    exact S.cells.mem_iff.mpr (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  have hfin : ∀ p ∈ S.finished,
      UsesOnePrimary nextOwner (Sum.inl p.1) (S.primary (p.1+1)) (scanOutput v fresh p.2) := by
    intro p hp
    by_cases he : Sum.inl p.1 = C.cls
    · have hh := (scanOutput_spec v fresh p.2 hvn).preserves_class
        (fun a => a = S.primary (p.1+1)) S.owner (Sum.inl p.1) (S.finished_alphabet p hp)
      simpa only [he] using hh
    · rw [scanOutput_eq_self v fresh p.2 hvn (C.outside_finished p hp he)]
      exact UsesClass.extend_other (S.finished_alphabet p hp)
        (S.partition.fresh_absent_cell hr p.2 (hfinmem p hp))
  have hpow : ∀ p ∈ S.powers,
      UsesOnePrimary nextOwner (Sum.inr p.1) (S.primary p.1) (scanOutput v fresh p.2) := by
    intro p hp
    by_cases he : Sum.inr p.1 = C.cls
    · have hh := (scanOutput_spec v fresh p.2 hvn).preserves_class
        (fun a => a = S.primary p.1) S.owner (Sum.inr p.1) (S.power_alphabet p hp)
      simpa only [he] using hh
    · rw [scanOutput_eq_self v fresh p.2 hvn (C.outside_powers p hp he)]
      exact UsesClass.extend_other (S.power_alphabet p hp)
        (S.partition.fresh_absent_cell hr p.2 (hpowmem p hp))
  have htarget : ∀ n ∈ targetNumbers h D,
      scanOutput v fresh (targetState n S.primary t) = targetState n S.primary t := by
    intro n hn
    apply scanOutput_eq_self v fresh _ hvn
    apply hprotected
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨n, hn, rfl⟩
  refine {
    wellFormed := hr.wellFormed S.wellFormed hvn
    generates := hr.preserves_word _ S.generates
    partition := S.partition.afterStep hr hv
    primary := S.primary
    primary_zero := S.primary_zero
    primary_injective := S.primary_injective
    primary_defined := ?_
    primary_not_start := ?_
    target_first := ?_
    target_rest := ?_
    owner := nextOwner
    primary_unowned := ?_
    marker_owned := ?_
    finished := S.nextFinished v fresh C
    powers := S.nextPowers v fresh C
    finished_indices := ?_
    power_indices := ?_
    finished_alphabet := ?_
    power_alphabet := ?_
    finished_noAdjacent := ?_
    cells := ?_ }
  · intro i hi hit
    rw [hr.domain]
    exact Finset.mem_insert_of_mem (S.primary_defined i hi hit)
  · intro i hi
    rw [hr.start]
    exact S.primary_not_start i hi
  · rw [Fragmentation.afterStep_first, S.target_first]
    exact htarget _ (targetNumbers_head_mem h D (by omega))
  · have he : (((S.partition.afterStep hr hv).rest).map Prod.snd).take
        ((targetNumbers h D).length-1) =
        ((S.partition.rest.map Prod.snd).take ((targetNumbers h D).length-1)).map (scanOutput v fresh) := by
      simp only [Fragmentation.afterStep_rest, List.map_map, List.map_take, Function.comp_def]
    rw [he, S.target_rest, List.map_map]
    apply List.map_congr_left
    intro n hn
    exact htarget n (List.mem_of_mem_tail hn)
  · intro i hi
    have hf := S.fresh_ne_primary (by omega) hD hr hvn i hi
    simp only [nextOwner, extendOwner, if_neg (Ne.symm hf), S.primary_unowned i hi]
  · intro j hj c
    have hf := S.fresh_ne_marker hr hvn j hj c
    simp only [nextOwner, extendOwner, if_neg (Ne.symm hf), S.marker_owned j hj c]
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact S.finished_indices q hq
    · cases he : C.cls with
      | inl j =>
        have hp' : p = (j,v) := by simpa only [he, List.mem_singleton] using hp
        subst p
        simpa only [he, classValid] using C.valid
      | inr u => simp only [he, List.not_mem_nil] at hp
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact S.power_indices q hq
    · cases he : C.cls with
      | inl j => simp only [he, List.not_mem_nil] at hp
      | inr u =>
        have hp' : p = (u,v) := by simpa only [he, List.mem_singleton] using hp
        subst p
        simpa only [he, classValid] using C.valid
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hfin q hq
    · cases he : C.cls with
      | inl j =>
        have hp' : p = (j,v) := by simpa only [he, List.mem_singleton] using hp
        subst p
        simpa only [he, classPrimary] using hnew
      | inr u => simp only [he, List.not_mem_nil] at hp
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hpow q hq
    · cases he : C.cls with
      | inl j => simp only [he, List.not_mem_nil] at hp
      | inr u =>
        have hp' : p = (u,v) := by simpa only [he, List.mem_singleton] using hp
        subst p
        simpa only [he, classPrimary] using hnew
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have hi := S.finished_indices q hq
      exact (scanOutput_spec v fresh q.2 hvn).preserves_noAdjacent
        (S.fresh_ne_primary (by omega) hD hr hvn (q.1+1) (by omega)) (S.finished_noAdjacent q hq)
    · cases he : C.cls with
      | inl j =>
        have hp' : p = (j,v) := by simpa only [he, List.mem_singleton] using hp
        subst p
        exact C.aux_noAdjacent j he
      | inr u => simp only [he, List.not_mem_nil] at hp
  · let guarded := (targetNumbers h D).map (fun n => targetState n S.primary t) ++
        unfinishedCells h t S.primary
    have he : guarded = (S.active ht).protectedCells := by
      unfold guarded
      rw [S.unfinished_split ht]
      simp only [guarded, ActiveStorage.protectedCells, active, List.map_map,
        Function.comp_def, List.append_assoc, List.singleton_append]
    have hmap : guarded.map (scanOutput v fresh) = guarded := by
      calc
        _ = guarded.map id := List.map_congr_left (fun w hw =>
          scanOutput_eq_self v fresh w hvn (hprotected w (he ▸ hw)))
        _ = _ := List.map_id _
    have hp := (S.partition.afterStep_pieces hr hv).trans
      ((S.cells.map (scanOutput v fresh)).append_right [v])
    change ((S.partition.afterStep hr hv).pieces).Perm
      ((guarded ++ S.finished.map Prod.snd ++ S.powers.map Prod.snd).map
        (scanOutput v fresh) ++ [v]) at hp
    rw [List.map_append, List.map_append, hmap] at hp
    apply hp.trans
    change ((guarded ++ (S.finished.map Prod.snd).map (scanOutput v fresh) ++
      (S.powers.map Prod.snd).map (scanOutput v fresh)) ++ [v]).Perm
      (guarded ++ (S.nextFinished v fresh C).map Prod.snd ++ (S.nextPowers v fresh C).map Prod.snd)
    cases he : C.cls with
    | inl j =>
      simp only [nextFinished, nextPowers, he, scannedTagged, List.map_append,
        List.map_cons, List.map_nil, List.append_nil, List.map_map, Function.comp_def]
      have hh := (List.perm_append_comm
        (l₁ := S.powers.map (fun p => scanOutput v fresh p.2)) (l₂ := [v])).append_left
          (guarded ++ S.finished.map (fun p => scanOutput v fresh p.2))
      simpa only [List.append_assoc, List.singleton_append] using hh
    | inr u =>
      apply List.Perm.of_eq
      simp only [nextFinished, nextPowers, he, scannedTagged, List.map_append,
        List.map_cons, List.map_nil, List.append_nil, List.map_map, Function.comp_def, List.append_assoc]

/-- The preservation result applied to an actual maximizing cleanup choice.
All classification and nonoccurrence premises are discharged here. -/
theorem cleanup_preserved {G H : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (ht : t < h) (hD : D.length = h^2)
    {v : Word Nat} {fresh : Nat} {counts : Nat → Nat}
    (hr : GlobalStep G H v fresh counts) (hv : G.Eligible v)
    (hne : v ≠ List.replicate 64 (S.primary t))
    (hmax : ∀ u, G.Eligible u → G.gain u ≤ G.gain v) :
    ∃ T : PhaseStorage H h D t, T.primary = S.primary := by
  obtain ⟨C⟩ := S.cleanup_choice_exists ht hD v hv hne hmax
  exact ⟨S.afterCleanup ht hD hr hv C (S.protected_untouched ht hD v hv hne hmax), rfl⟩

/-- The complete within-phase forcing theorem, allowing any number of cleanup
rounds and every tie resolution. The next primary substitution occurs in any
terminal continuation of a grammar satisfying the established phase model. -/
theorem forces_primary {G H : Grammar} {h t n : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (ht : t < h) (hD : D.length = h^2)
    (run : GreedyRun G H n) (hterm : H.Terminal) :
    ∃ K L m k, GreedyRun G K m ∧ (∃ T : PhaseStorage K h D t, T.primary = S.primary) ∧
      GreedyStep K L ∧
      (∃ fresh, GlobalStep K L (List.replicate 64 (S.primary t)) fresh
        (fun i => scanCount (List.replicate 64 (S.primary t)) (K.rhs i))) ∧
      GreedyRun L H k ∧ n = m+1+k := by
  let P : Grammar → Prop := fun K => ∃ T : PhaseStorage K h D t, T.primary = S.primary
  let event : Grammar → Grammar → Prop := fun K L =>
    ∃ fresh, GlobalStep K L (List.replicate 64 (S.primary t)) fresh
      (fun i => scanCount (List.replicate 64 (S.primary t)) (K.rhs i))
  apply run.forces_event P event ⟨S, rfl⟩ hterm
  · intro K hK
    obtain ⟨T, hT⟩ := hK
    refine ⟨List.replicate 64 (T.primary t), (T.active ht).benchmark_eligible ?_⟩
    rw [T.active_current_length ht]
    have hh := auxiliaryLength_gt_mass h (t+1) (by omega) (by omega)
    omega
  · intro K L hK hs hne
    obtain ⟨T, hT⟩ := hK
    obtain ⟨v, fresh, hr, hv, hm⟩ := hs
    have hvne : v ≠ List.replicate 64 (T.primary t) := by
      intro he
      apply hne
      refine ⟨fresh, ?_⟩
      simpa only [he, hT] using hr
    obtain ⟨U, hU⟩ := T.cleanup_preserved ht hD hr hv hvne hm
    exact ⟨U, hU.trans hT⟩

end PhaseStorage

end GreedyLowerBound
