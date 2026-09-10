import GreedyLowerBound.TerminalSymbols

set_option autoImplicit false

namespace GreedyLowerBound

abbrev StorageClass := Sum Nat Nat

/-- Auxiliary j's word after t prescribed substitutions, with j and t both
zero based. Only j ≥ t is used while that auxiliary is unfinished. -/
def unfinishedCells (h t : Nat) (A : Nat → Nat) : List (Word Nat) :=
  (List.range (h-t)).map (fun s =>
    paddedRuns (A t) (64^(s+1)) (auxiliaryMarkers h (t+s)))

/-- The literal part of the full phase invariant. Finished auxiliary classes
are indexed by `Sum.inl j`; power-definition layers by `Sum.inr u`. Every
cell, including every additional rule, occurs in the exhaustive permutation.
No assertion of reachability or phase preservation is built into this data. -/
structure PhaseStorage (G : Grammar) (h : Nat) (D : List Bool) (t : Nat) where
  wellFormed : G.WellFormed
  generates : G.Generates (inputWord h D)
  partition : Fragmentation G
  primary : Nat → Nat
  primary_zero : primary 0 = 0
  primary_injective : Function.Injective primary
  primary_defined : ∀ i, 0 < i → i ≤ t → primary i ∈ G.defined
  primary_not_start : ∀ i ≤ t, primary i ≠ G.start
  target_first : partition.first = targetState ((targetNumbers h D).headD 0) primary t
  target_rest : (partition.rest.map Prod.snd).take ((targetNumbers h D).length-1) =
    (targetNumbers h D).tail.map (fun n => targetState n primary t)
  owner : Nat → Option StorageClass
  primary_unowned : ∀ i ≤ t, owner (primary i) = none
  marker_owned : ∀ j < h, ∀ c : Letter, owner (markerName j c) = some (Sum.inl j)
  finished : List (Nat × Word Nat)
  powers : List (Nat × Word Nat)
  finished_indices : ∀ p ∈ finished, p.1 < t
  power_indices : ∀ p ∈ powers, p.1 < t
  finished_alphabet : ∀ p ∈ finished,
    UsesOnePrimary owner (Sum.inl p.1) (primary (p.1+1)) p.2
  power_alphabet : ∀ p ∈ powers, UsesOnePrimary owner (Sum.inr p.1) (primary p.1) p.2
  finished_noAdjacent : ∀ p ∈ finished, NoAdjacent (primary (p.1+1)) p.2
  cells : partition.pieces.Perm
    ((targetNumbers h D).map (fun n => targetState n primary t) ++ unfinishedCells h t primary ++
      finished.map Prod.snd ++ powers.map Prod.snd)

theorem NoAdjacent.of_absent (X : Nat) (w : Word Nat) (hw : X ∉ w) : NoAdjacent X w := by
  intro hin
  exact hw (hin.subset (by simp))

theorem UsesOnePrimary.absent_other {κ : Type} {owner : Nat → Option κ}
    {C : κ} {X Y : Nat} {w : Word Nat} (hw : UsesOnePrimary owner C X w)
    (hy : owner Y = none) (hxy : Y ≠ X) : Y ∉ w := by
  intro hm
  rcases hw Y hm with he | he
  · exact hxy he
  · rw [hy] at he
    contradiction

def initialOwner (h a : Nat) : Option StorageClass :=
  if a = 0 then none else if a ≤ 3*h then some (Sum.inl ((a-1)/3)) else none

theorem initialOwner_marker (h j : Nat) (hj : j < h) (c : Letter) :
    initialOwner h (markerName j c) = some (Sum.inl j) := by
  have hc := c.isLt
  have hz := markerName_pos j c
  have hle : markerName j c ≤ 3*h := by unfold markerName; omega
  have hdiv : (markerName j c-1)/3 = j := by unfold markerName; omega
  simp only [initialOwner, if_neg (Nat.ne_of_gt hz), if_pos hle, hdiv]

/-- Initialization of every literal class in the phase model. -/
noncomputable def initialPhaseStorage (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) :
    PhaseStorage (inputGrammar h D) h D 0 where
  wellFormed := inputGrammar_wellFormed h D hh hD
  generates := inputGrammar_generates h D
  partition := inputPartition h D
  primary := id
  primary_zero := rfl
  primary_injective := Function.injective_id
  primary_defined := by intros; omega
  primary_not_start := by
    intro i hi he
    have hi' : i = 0 := by omega
    have hm : 0 ∈ (inputGrammar h D).defined := by
      rw [← show (inputGrammar h D).start = 0 from by simpa [hi'] using he.symm]
      exact (inputGrammar_wellFormed h D hh hD).1
    exact Grammar.generated_symbol_terminal (inputGrammar_wellFormed h D hh hD)
      (inputGrammar_generates h D) 0 (inputWord_contains_zero h D hh hD) hm
  target_first := by simp [inputPartition, initialFragmentation, inputFirst, targetState_initial]
  target_rest := by
    change ((numberedRest (1+3*h) (inputRest h D)).map Prod.snd).take
      ((targetNumbers h D).length-1) = _
    rw [numberedRest_words]
    simp only [inputRest, targetState_initial, id_eq]
    have he : ((targetNumbers h D).tail.map (fun n => List.replicate n 0)).length =
        (targetNumbers h D).length-1 := by simp
    rw [← he, List.take_left]
  owner := initialOwner h
  primary_unowned := by
    intro i hi
    have he : i = 0 := by omega
    simp [he, initialOwner]
  marker_owned := initialOwner_marker h
  finished := []
  powers := []
  finished_indices := by simp
  power_indices := by simp
  finished_alphabet := by simp
  power_alphabet := by simp
  finished_noAdjacent := by simp
  cells := by
    apply List.Perm.of_eq
    rw [inputPartition_pieces h D hh]
    simp only [targetState_initial, List.map_nil, List.append_nil,
      unfinishedCells, Nat.sub_zero, Nat.zero_add, id_eq]
    apply congrArg (List.append ((targetNumbers h D).map (fun n => List.replicate n 0)))
    exact List.map_congr_left (fun j _ => inputAuxiliary_padded h j)

theorem UsesOnePrimary.padded {κ : Type} (owner : Nat → Option κ) (C : κ)
    (X L : Nat) (w : Word Nat) (hw : ∀ a ∈ w, owner a = some C) :
    UsesOnePrimary owner C X (paddedRuns X L w) := by
  intro a ha
  obtain ⟨z, hz, ha⟩ := List.mem_flatMap.mp ha
  rcases List.mem_append.mp ha with ha | ha
  · exact Or.inl (List.mem_replicate.mp ha).2
  · have he : a = z := by simpa using ha
    exact Or.inr (he ▸ hw z hz)

namespace PhaseStorage

theorem fresh_ne_primary {G H : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (hh : 1 ≤ h) (hD : D.length = h^2)
    {v : Word Nat} {fresh : Nat} {counts : Nat → Nat}
    (hr : GlobalStep G H v fresh counts) (hv : v ≠ []) (i : Nat) (hi : i ≤ t) :
    fresh ≠ S.primary i := by
  by_cases hi0 : i = 0
  · rw [hi0, S.primary_zero]
    exact hr.fresh_ne_input_symbol S.wellFormed S.generates hv 0
      (inputWord_contains_zero h D hh hD)
  · intro he
    exact hr.fresh_defined (he ▸ S.primary_defined i (by omega) hi)

theorem fresh_ne_marker {G H : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) {v : Word Nat} {fresh : Nat} {counts : Nat → Nat}
    (hr : GlobalStep G H v fresh counts) (hv : v ≠ []) (j : Nat) (hj : j < h) (c : Letter) :
    fresh ≠ markerName j c := hr.fresh_ne_input_symbol S.wellFormed S.generates hv _
      (inputWord_contains_marker h D j hj c)

theorem active_ne_marker {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (j : Nat) (hj : j < h) (c : Letter) :
    markerName j c ≠ S.primary t := by
  intro he
  have ho := S.marker_owned j hj c
  rw [he, S.primary_unowned t (Nat.le_refl _)] at ho
  contradiction

theorem active_ne_markers {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (j : Nat) (hj : j < h) (z : Nat)
    (hz : z ∈ auxiliaryMarkers h j) : z ≠ S.primary t := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
  exact S.active_ne_marker j hj c

theorem cleanup_no_active_adjacent {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (w : Word Nat)
    (hw : w ∈ S.finished.map Prod.snd ++ S.powers.map Prod.snd) :
    NoAdjacent (S.primary t) w := by
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    by_cases he : p.1+1 = t
    · simpa [he] using S.finished_noAdjacent p hp
    · apply NoAdjacent.of_absent
      exact (S.finished_alphabet p hp).absent_other
        (S.primary_unowned t (Nat.le_refl _))
        (fun hh => he (S.primary_injective hh).symm)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    have hi := S.power_indices p hp
    apply NoAdjacent.of_absent
    exact (S.power_alphabet p hp).absent_other
      (S.primary_unowned t (Nat.le_refl _)) (by intro he; have hh := S.primary_injective he; omega)

theorem unfinished_split {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (ht : t < h) :
    unfinishedCells h t S.primary =
      paddedRuns (S.primary t) 64 (auxiliaryMarkers h t) ::
        (List.range (h-t-1)).map (fun s =>
          paddedRuns (S.primary t) (64*64^(s+1)) (auxiliaryMarkers h (t+(s+1)))) := by
  have he : h-t = (h-t-1)+1 := by omega
  unfold unfinishedCells
  conv_lhs => rw [he, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.zero_add, Nat.add_zero, Nat.pow_one]
  congr 1
  apply List.map_congr_left
  intro s hs
  simp only [Function.comp_def]
  have hp : 64^(s+1+1) = 64*64^(s+1) := by rw [Nat.pow_succ, Nat.mul_comm]
  exact congrArg (fun L => paddedRuns (S.primary t) L (auxiliaryMarkers h (t+(s+1)))) hp

/-- The previously proved active-unary model follows from the full literal
class invariant; no occurrence-count assumptions are added. -/
noncomputable def active {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (ht : t < h) : ActiveStorage G (S.primary t) where
  partition := S.partition
  targets := (targetNumbers h D).map (fun n => targetState n S.primary t)
  current := auxiliaryMarkers h t
  later := (List.range (h-t-1)).map (fun s => (64^(s+1), auxiliaryMarkers h (t+(s+1))))
  cleanup := S.finished.map Prod.snd ++ S.powers.map Prod.snd
  current_markers := S.active_ne_markers t ht
  later_markers := by
    intro p hp z hz
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
    have hi := List.mem_range.mp hs
    exact S.active_ne_markers (t+(s+1)) (by omega) z hz
  cleanup_noAdjacent := S.cleanup_no_active_adjacent
  cells := by
    have hh := S.cells
    rw [S.unfinished_split ht] at hh
    simpa only [List.map_map, Function.comp_def, List.append_assoc, List.singleton_append] using hh

theorem active_target_mass {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (ht : t < h) (hD : D.length = h^2) :
    cellMass (S.active ht).targets ≤ targetMass h := by
  have he : cellMass (S.active ht).targets =
      ((targetNumbers h D).map (fun n => (targetState n S.primary t).length)).sum := by
    simp [cellMass, active, List.map_map, Function.comp_def]
  rw [he]
  apply Nat.le_trans _ (targetNumbers_sum_le h D hD)
  have haux : ∀ ns : List Nat,
      (ns.map (fun n => (targetState n S.primary t).length)).sum ≤ ns.sum := by
    intro ns
    induction ns with
    | nil => simp
    | cons n ns ih =>
      have hn := targetState_length_le n S.primary t S.primary_injective
      simp only [List.map_cons, List.sum_cons]
      omega
  exact haux _

theorem active_current_length {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (ht : t < h) :
    (S.active ht).current.length = auxiliaryLength h (t+1) := auxiliaryMarkers_length h t

theorem active_later_mass {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (ht : t < h) :
    (S.active ht).laterMass = laterAuxiliaryMass h (t+1) := by
  unfold ActiveStorage.laterMass
  change (((List.range (h-t-1)).map (fun s =>
    (64^(s+1), auxiliaryMarkers h (t+(s+1))))).map (fun p => p.2.length*(64*p.1))).sum = _
  rw [List.map_map, sum_map_range_eq]
  have he : h-t-1 = h-(t+1) := by omega
  rw [he]
  unfold laterAuxiliaryMass
  apply Finset.sum_congr rfl
  intro s hs
  simp only [Function.comp_def, auxiliaryMarkers_length, phaseWeight]
  have hi : t+(s+1)+1 = (t+1)+(s+1) := by omega
  rw [hi]
  simp only [Nat.pow_succ]
  ac_rfl

theorem unary_loses {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (ht : t < h) (hD : D.length = h^2)
    (d : Nat) (hd : d ≠ 64) (hv : G.Eligible (List.replicate d (S.primary t))) :
    G.gain (List.replicate d (S.primary t)) < G.gain (List.replicate 64 (S.primary t)) := by
  apply (S.active ht).unary_loses (targetMass h) d (S.active_target_mass ht hD) _ _ hd hv
  · rw [S.active_current_length ht]
    have hh := auxiliaryLength_gt_mass h (t+1) (by omega) (by omega)
    omega
  · rw [S.active_current_length ht, S.active_later_mass ht]
    exact laterAuxiliaryMass_lt h (t+1) (by omega)

def otherCells {G : Grammar} {h t : Nat} {D : List Bool} (S : PhaseStorage G h D t) :
    List (StorageClass × Nat × Word Nat) :=
  (List.range (h-t)).map (fun s => (Sum.inl (t+s), S.primary t,
      paddedRuns (S.primary t) (64^(s+1)) (auxiliaryMarkers h (t+s)))) ++
    S.finished.map (fun p => (Sum.inl p.1, S.primary (p.1+1), p.2)) ++
    S.powers.map (fun p => (Sum.inr p.1, S.primary p.1, p.2))

theorem otherCells_words {G : Grammar} {h t : Nat} {D : List Bool} (S : PhaseStorage G h D t) :
    S.otherCells.map (fun p => p.2.2) =
      unfinishedCells h t S.primary ++ S.finished.map Prod.snd ++ S.powers.map Prod.snd := by
  simp [otherCells, unfinishedCells, List.map_map, Function.comp_def]

theorem otherCells_alphabet {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (p : StorageClass × Nat × Word Nat) (hp : p ∈ S.otherCells) :
    UsesOnePrimary S.owner p.1 p.2.1 p.2.2 := by
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
      have hi := List.mem_range.mp hs
      apply UsesOnePrimary.padded
      intro a ha
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
      exact S.marker_owned (t+s) (by omega) c
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact S.finished_alphabet q hq
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact S.power_alphabet q hq

theorem target_loses {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (ht : t < h) (hD : D.length = h^2)
    (n : Nat) (hn : n ∈ targetNumbers h D) (v : Word Nat) (hv : G.Eligible v)
    (hne : v ≠ List.replicate 64 (S.primary t))
    (hc : 0 < scanCount v (targetState n S.primary t)) :
    G.gain v < G.gain (List.replicate 64 (S.primary t)) := by
  have hpieces : (S.active ht).partition.pieces.Perm
      ((S.active ht).targets ++ S.otherCells.map (fun c => c.2.2)) := by
    rw [S.otherCells_words]
    simpa only [List.append_assoc] using S.cells
  apply (S.active ht).factor_in_target_loses S.primary t S.owner S.otherCells hpieces
    S.otherCells_alphabet S.primary_injective S.primary_unowned (targetMass h) n
    (S.active_target_mass ht hD) _ _ _ v hv hne hc
  · rw [S.active_current_length ht]
    have hh := auxiliaryLength_gt_mass h (t+1) (by omega) (by omega)
    omega
  · rw [S.active_current_length ht, S.active_later_mass ht]
    exact laterAuxiliaryMass_lt h (t+1) (by omega)
  · intro u hu
    obtain ⟨s, hs, i, hi, rfl⟩ := targetNumbers_mem h D n hn
    exact targetNumber_digits h D s i u

end PhaseStorage

end GreedyLowerBound
