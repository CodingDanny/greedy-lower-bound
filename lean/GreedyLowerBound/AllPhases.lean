import GreedyLowerBound.PhaseAdvance

set_option autoImplicit false

namespace GreedyLowerBound

/-- A trace of actual prescribed substitutions with arbitrary Greedy cleanup
between them. Names refer to a single final injective primary-name function. -/
inductive PrimaryEvents (A : Nat → Nat) : Nat → Nat → Grammar → Grammar → Prop
  | nil (t : Nat) (G : Grammar) : PrimaryEvents A t t G G
  | cons {t k m : Nat} {G K L H : Grammar}
      (preRun : GreedyRun G K m) (step : GreedyStep K L)
      (primary : GlobalStep K L (List.replicate 64 (A t)) (A (t+1))
        (fun i => scanCount (List.replicate 64 (A t)) (K.rhs i)))
      (tail : PrimaryEvents A (t+1) k L H) : PrimaryEvents A t k G H

/-- All remaining prescribed phases occur in any terminal continuation. The
result includes the complete intermediate phase model, an actual event trace,
and preservation of every primary name already assigned on entry. -/
theorem PhaseStorage.complete {G H : Grammar} {h t n : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (ht : t ≤ h) (hD : D.length = h^2)
    (run : GreedyRun G H n) (hterm : H.Terminal) :
    ∃ K m k, ∃ T : PhaseStorage K h D h,
      GreedyRun G K m ∧ PrimaryEvents T.primary t h G K ∧
      (∀ i ≤ t, T.primary i = S.primary i) ∧ GreedyRun K H k ∧
      n = m+k ∧ h-t ≤ m := by
  have aux : ∀ r G t, t ≤ h → ∀ S : PhaseStorage G h D t, GreedyRun G H r →
      ∃ K m k, ∃ T : PhaseStorage K h D h,
        GreedyRun G K m ∧ PrimaryEvents T.primary t h G K ∧
        (∀ i ≤ t, T.primary i = S.primary i) ∧ GreedyRun K H k ∧
        r = m+k ∧ h-t ≤ m := by
    intro r
    induction r using Nat.strongRecOn with
    | ind r ih =>
      intro G t ht S run
      by_cases he : t = h
      · subst t
        exact ⟨G, 0, r, S, GreedyRun.nil G, PrimaryEvents.nil h G,
          (fun _ _ => rfl), run, by omega, by omega⟩
      · have hlt : t < h := by omega
        obtain ⟨K, L, m, k, hpre, ⟨U, hU⟩, hstep, ⟨fresh, hr⟩, hrest, htime⟩ :=
          S.forces_primary hlt hD run hterm
        have hr' : GlobalStep K L (List.replicate 64 (U.primary t)) fresh
            (fun i => scanCount (List.replicate 64 (U.primary t)) (K.rhs i)) := by
          rw [hU]
          exact hr
        let V := U.advance hlt hD hr'
        have hVnew : V.primary (t+1) = fresh := advancePrimaries_new U.primary t fresh
        have hVold : ∀ i ≤ t, V.primary i = S.primary i := by
          intro i hi
          have hf := U.fresh_ne_primary (by omega) hD hr' (by simp)
          have hh := advancePrimaries_old U.primary U.primary_injective t fresh hf i hi
          exact hh.trans (congrFun hU i)
        obtain ⟨Z, p, q, T, hLZ, events, hagree, hZH, hk, hcount⟩ :=
          ih k (by omega) L (t+1) (by omega) V hrest
        have hAold : ∀ i ≤ t, T.primary i = S.primary i :=
          fun i hi => (hagree i (by omega)).trans (hVold i hi)
        have hAnew : T.primary (t+1) = fresh :=
          (hagree (t+1) (Nat.le_refl _)).trans hVnew
        have hround : GlobalStep K L (List.replicate 64 (T.primary t)) (T.primary (t+1))
            (fun i => scanCount (List.replicate 64 (T.primary t)) (K.rhs i)) := by
          rw [hAold t (Nat.le_refl _), hAnew]
          exact hr
        refine ⟨Z, m+(p+1), q, T, hpre.trans (GreedyRun.cons hstep hLZ),
          PrimaryEvents.cons hpre hstep hround events, hAold, hZH, ?_, ?_⟩ <;> omega
  exact aux n G t ht S run

/-- Section 4 for the actual constructed input, uniformly over all seeds of
length h² and all terminal Greedy executions. De Bruijn uniqueness is not
needed for forcing; it is needed later for the factor-count lower bound. -/
theorem input_all_phases (h : Nat) (D : List Bool) (hh : 1 ≤ h) (hD : D.length = h^2)
    (H : Grammar) (n : Nat) (run : GreedyRun (inputGrammar h D) H n) (hterm : H.Terminal) :
    ∃ K m k, ∃ T : PhaseStorage K h D h,
      GreedyRun (inputGrammar h D) K m ∧ PrimaryEvents T.primary 0 h (inputGrammar h D) K ∧
      GreedyRun K H k ∧ n = m+k ∧ h ≤ m := by
  obtain ⟨K, m, k, T, hp, he, ha, ht, hn, hm⟩ :=
    (initialPhaseStorage h D hh hD).complete (by omega) hD run hterm
  exact ⟨K, m, k, T, hp, he, ht, hn, by simpa using hm⟩

end GreedyLowerBound
