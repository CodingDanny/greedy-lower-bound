import GreedyLowerBound.PhaseExclusion

set_option autoImplicit false

namespace GreedyLowerBound

def classPrimary (A : Nat → Nat) : StorageClass → Nat
  | Sum.inl j => A (j+1)
  | Sum.inr u => A u

def classValid (t : Nat) : StorageClass → Prop
  | Sum.inl j => j < t
  | Sum.inr u => u < t

theorem UsesOnePrimary.of_infix {κ : Type} {owner : Nat → Option κ}
    {C : κ} {X : Nat} {v w : Word Nat} (hw : UsesOnePrimary owner C X w)
    (hv : v.IsInfix w) : UsesOnePrimary owner C X v := fun a ha => hw a (hv.subset ha)

/-- A selected cleanup factor belongs to exactly one eligible storage class;
the outside-count fields make the global ownership assertion explicit. -/
structure CleanupChoice {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (v : Word Nat) where
  cls : StorageClass
  valid : classValid t cls
  alphabet : UsesOnePrimary S.owner cls (classPrimary S.primary cls) v
  aux_noAdjacent : ∀ j, cls = Sum.inl j → NoAdjacent (S.primary (j+1)) v
  outside_finished : ∀ p ∈ S.finished, Sum.inl p.1 ≠ cls → scanCount v p.2 = 0
  outside_powers : ∀ p ∈ S.powers, Sum.inr p.1 ≠ cls → scanCount v p.2 = 0

namespace PhaseStorage

def privateCleanupChoice {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (v : Word Nat) (C : StorageClass)
    (hC : classValid t C) (hv : UsesOnePrimary S.owner C (classPrimary S.primary C) v)
    (haux : ∀ j, C = Sum.inl j → NoAdjacent (S.primary (j+1)) v)
    (a : Nat) (ha : a ∈ v) (ho : S.owner a = some C) : CleanupChoice S v where
  cls := C
  valid := hC
  alphabet := hv
  aux_noAdjacent := haux
  outside_finished := by
    intro p hp hne
    have hi := S.finished_indices p hp
    apply scanCount_zero_of_missing v p.2 a ha
    exact (S.finished_alphabet p hp).absent_private
      (S.primary_unowned (p.1+1) (by omega)) ho hne
  outside_powers := by
    intro p hp hne
    have hi := S.power_indices p hp
    apply scanCount_zero_of_missing v p.2 a ha
    exact (S.power_alphabet p hp).absent_private (S.primary_unowned p.1 (by omega)) ho hne

/-- Section 4.5's complete remaining-factor classification, covering private
symbols and purely primary factors, and every additional right-hand side. -/
theorem cleanup_choice_exists {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (ht : t < h) (hD : D.length = h^2)
    (v : Word Nat) (hv : G.Eligible v) (hne : v ≠ List.replicate 64 (S.primary t))
    (hmax : ∀ u, G.Eligible u → G.gain u ≤ G.gain v) : Nonempty (CleanupChoice S v) := by
  have hp := S.protected_untouched ht hD v hv hne hmax
  obtain ⟨w, hw, hin⟩ := (S.active ht).cleanup_contains_selected v hv hp
  change w ∈ S.finished.map Prod.snd ++ S.powers.map Prod.snd at hw
  have hvn : v ≠ [] := by intro he; have hh := hv.1; simp [he] at hh
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    have hi := S.finished_indices p hp
    have hal := (S.finished_alphabet p hp).of_infix hin
    obtain ⟨a, ha, hax⟩ := (S.finished_noAdjacent p hp).factor_has_other hin hv.1
    have ho : S.owner a = some (Sum.inl p.1) := (hal a ha).resolve_left hax
    refine ⟨S.privateCleanupChoice v (Sum.inl p.1) hi hal ?_ a ha ho⟩
    intro j he
    have he' := Sum.inl.inj he
    simpa only [← he'] using (S.finished_noAdjacent p hp).of_infix hin
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    have hi := S.power_indices p hp
    have hal := (S.power_alphabet p hp).of_infix hin
    by_cases hall : ∀ a ∈ v, a = S.primary p.1
    · have he : v = List.replicate v.length (S.primary p.1) := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil v hvn
      have ham : S.primary p.1 ∈ v := (hall a ha) ▸ ha
      refine ⟨{
        cls := Sum.inr p.1
        valid := hi
        alphabet := hal
        aux_noAdjacent := by intros; contradiction
        outside_finished := ?_
        outside_powers := ?_ }⟩
      · intro q hq hneq
        by_cases heq : q.1+1 = p.1
        · have hn := S.finished_noAdjacent q hq
          rw [heq] at hn
          have hh := scanCount_zero_of_noAdjacent (S.primary p.1) v.length q.2 hv.1 hn
          rw [← he] at hh
          exact hh
        · apply scanCount_zero_of_missing v q.2 (S.primary p.1) ham
          exact (S.finished_alphabet q hq).absent_other
            (S.primary_unowned p.1 (by omega))
            (by intro h; exact heq (S.primary_injective h).symm)
      · intro q hq hneq
        apply scanCount_zero_of_missing v q.2 (S.primary p.1) ham
        exact (S.power_alphabet q hq).absent_other (S.primary_unowned p.1 (by omega))
          (by intro he; exact hneq (congrArg Sum.inr (S.primary_injective he).symm))
    · have hex : ∃ a ∈ v, a ≠ S.primary p.1 := by
        by_contra hn
        apply hall
        intro a ha
        by_contra hne
        exact hn ⟨a, ha, hne⟩
      obtain ⟨a, ha, hax⟩ := hex
      have ho : S.owner a = some (Sum.inr p.1) := (hal a ha).resolve_left hax
      exact ⟨S.privateCleanupChoice v (Sum.inr p.1) hi hal (by intros; contradiction) a ha ho⟩

end PhaseStorage

end GreedyLowerBound
