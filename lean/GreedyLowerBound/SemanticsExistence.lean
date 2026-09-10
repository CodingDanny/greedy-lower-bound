import GreedyLowerBound.GrammarSemantics

set_option autoImplicit false
namespace GreedyLowerBound.Grammar

/-- A finite unfolding; fuel zero leaves symbols literal. -/
def unfoldFor (G : Grammar) : Nat → Nat → Word Nat
  | 0, i => [i]
  | n+1, i => if i ∈ G.defined then (G.rhs i).flatMap (G.unfoldFor n) else [i]

theorem unfoldFor_terminal (G : Grammar) (n i : Nat) (hi : i ∉ G.defined) :
    G.unfoldFor n i = [i] := by
  cases n <;> simp [unfoldFor, hi]

/-- Any fuel exceeding the nonterminal rank gives the same expansion. -/
theorem unfoldFor_stable (G : Grammar) (rank : Nat → Nat)
    (hr : ∀ i ∈ G.defined, ∀ j ∈ G.defined, j ∈ G.rhs i → rank j < rank i)
    (i n m : Nat) (hn : rank i < n) (hm : rank i < m) :
    G.unfoldFor n i = G.unfoldFor m i := by
  have aux : ∀ k i, rank i = k → ∀ n m, rank i < n → rank i < m →
      G.unfoldFor n i = G.unfoldFor m i := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro i hi n m hn hm
      cases n with
      | zero => omega
      | succ n =>
        cases m with
        | zero => omega
        | succ m =>
          by_cases hid : i ∈ G.defined
          · simp only [unfoldFor, if_pos hid]
            apply List.flatMap_congr
            intro j hj
            by_cases hjd : j ∈ G.defined
            · have hjr := hr i hid j hjd hj
              exact ih (rank j) (by omega) j rfl n m (by omega) (by omega)
            · rw [G.unfoldFor_terminal n j hjd, G.unfoldFor_terminal m j hjd]
          · simp only [unfoldFor, if_neg hid]
  exact aux (rank i) i rfl n m hn hm

/-- Every finite acyclic grammar has an interpretation satisfying all its
expansion equations. Existence is proved, not assumed as part of well-formedness. -/
theorem semantics_exists (G : Grammar) (hG : G.WellFormed) :
    ∃ value, G.Semantics value := by
  obtain ⟨_, _, rank, hr⟩ := hG
  let value := fun i => G.unfoldFor (rank i+1) i
  refine ⟨value, ?_, ?_⟩
  · intro i hi
    change G.unfoldFor (rank i+1) i = (G.rhs i).flatMap value
    rw [unfoldFor, if_pos hi]
    apply List.flatMap_congr
    intro j hj
    by_cases hjd : j ∈ G.defined
    · exact G.unfoldFor_stable rank hr j (rank i) (rank j+1)
        (hr i hi j hjd hj) (by omega)
    · change G.unfoldFor (rank i) j = G.unfoldFor (rank j+1) j
      rw [G.unfoldFor_terminal _ _ hjd, G.unfoldFor_terminal _ _ hjd]
  · intro i hi
    exact G.unfoldFor_terminal _ _ hi

theorem generates_exists (G : Grammar) (hG : G.WellFormed) :
    ∃ w, G.Generates w := by
  obtain ⟨value, hv⟩ := G.semantics_exists hG
  exact ⟨value G.start, value, hv, rfl⟩

end GreedyLowerBound.Grammar
