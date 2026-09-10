import GreedyLowerBound.TargetDigits

set_option autoImplicit false

namespace GreedyLowerBound

namespace Grammar

/-- The initial one-rule grammar S → w. The caller chooses a start symbol
absent from the input alphabet. -/
def initial (w : Word Nat) (start : Nat) : Grammar where
  defined := {start}
  rhs := fun i => if i = start then w else []
  start := start

theorem initial_size (w : Word Nat) (start : Nat) : (initial w start).size = w.length := by
  simp [initial, size]

theorem initial_wellFormed (w : Word Nat) (start : Nat) (hw : w ≠ [])
    (hs : start ∉ w) : (initial w start).WellFormed := by
  refine ⟨by simp [initial], ?_, fun _ => 0, ?_⟩
  · intro i hi
    have he : i = start := by simpa [initial] using hi
    subst i
    simpa [initial] using hw
  · intro i hi j hj hm
    have he : i = start := by simpa [initial] using hi
    have he' : j = start := by simpa [initial] using hj
    subst i
    subst j
    exact False.elim (hs (by simpa [initial] using hm))

theorem initial_generates (w : Word Nat) (start : Nat) (hs : start ∉ w) :
    (initial w start).Generates w := by
  let value : Nat → Word Nat := fun i => if i = start then w else [i]
  have he : w.flatMap value = w := by
    calc
      _ = w.flatMap (fun i => [i]) := by
        simp only [List.flatMap_def]
        apply congrArg List.flatten
        apply List.map_congr_left
        intro i hi
        have hn : i ≠ start := by intro he; subst i; exact hs hi
        simp [value, hn]
      _ = _ := List.flatMap_singleton' _
  refine ⟨value, ⟨?_, ?_⟩, by simp [value, initial]⟩
  · intro i hi
    have hi' : i = start := by simpa [initial] using hi
    subst i
    simpa [initial, value] using he.symm
  · intro i hi
    have hi' : i ≠ start := by simpa [initial] using hi
    simp [value, hi']

theorem initial_separator (w : Word Nat) (start z : Nat)
    (hz : w.count z = 1) (hs : z ≠ start) : (initial w start).StartSeparator z := by
  refine ⟨by simp [initial], by simpa [initial] using hs, ?_⟩
  intro i hi
  have hi' : i = start := by simpa [initial] using hi
  subst i
  simpa [initial] using hz

/-- A complete execution ends when no eligible factor remains. -/
def Terminal (G : Grammar) : Prop := ∀ v, ¬ G.Eligible v

end Grammar

theorem GreedyRun.trans {G H K : Grammar} {m n : Nat}
    (h : GreedyRun G H m) (h' : GreedyRun H K n) : GreedyRun G K (m+n) := by
  induction h with
  | nil => simpa using h'
  | cons hs ht ih => simpa only [Nat.add_assoc, Nat.add_comm 1 n] using GreedyRun.cons hs (ih h')

/-- The finite-run forcing principle in Section 4.6. Its hypotheses expose
exactly what a phase invariant must establish: a live competitor and
preservation until the prescribed event. The event then occurs under every
tie resolution represented by the supplied terminal run. -/
theorem GreedyRun.forces_event {G H : Grammar} {n : Nat} (run : GreedyRun G H n)
    (P : Grammar → Prop) (event : Grammar → Grammar → Prop)
    (hinit : P G) (hterm : H.Terminal)
    (hlive : ∀ K, P K → ∃ v, K.Eligible v)
    (hkeep : ∀ K L, P K → GreedyStep K L → ¬ event K L → P L) :
    ∃ K L m k, GreedyRun G K m ∧ P K ∧ GreedyStep K L ∧ event K L ∧
      GreedyRun L H k ∧ n = m+1+k := by
  induction run with
  | nil G =>
    obtain ⟨v, hv⟩ := hlive G hinit
    exact False.elim (hterm v hv)
  | @cons G K H n hs ht ih =>
    by_cases he : event G K
    · exact ⟨G, K, 0, n, GreedyRun.nil G, hinit, hs, he, ht, by omega⟩
    · have hK := hkeep G K hinit hs he
      obtain ⟨L, M, m, k, hr, hL, hs', he', ht', hn⟩ := ih hK hterm
      exact ⟨L, M, m+1, k, GreedyRun.cons hs hr, hL, hs', he', ht', by omega⟩

end GreedyLowerBound
