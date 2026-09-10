import GreedyLowerBound.FinalTheorem
import GreedyLowerBound.PaperAlgorithm

set_option autoImplicit false
namespace GreedyLowerBound

/-- The quantitative lower bound stated directly for the source paper's
maximal-string algorithm and its original stopping condition. -/
theorem paper_greedy_logarithmic_lower_bound (N : Nat) :
    ∃ r, 10 ≤ r ∧ N ≤ (hardWord r).length ∧
      (∃ H steps, PaperGreedyRun (hardGrammar r) H steps ∧ PaperTerminal H) ∧
      ∀ H steps, PaperGreedyRun (hardGrammar r) H steps → PaperTerminal H →
        Real.logb 2 ((hardWord r).length : Real) /
            (1200000 * Real.logb 2 (Real.logb 2 ((hardWord r).length : Real))) ≤
          approximationRatio (hardWord r) H := by
  obtain ⟨r, hr, hn, hex, hall⟩ := greedy_logarithmic_lower_bound N
  refine ⟨r, hr, hn, ?_, ?_⟩
  · obtain ⟨H, steps, run, ht⟩ := hex
    exact ⟨H, steps, (paperGreedyRun_iff _ _ _).mpr run, (paperTerminal_iff _).mpr ht⟩
  · intro H steps run ht
    exact hall H steps ((paperGreedyRun_iff _ _ _).mp run) ((paperTerminal_iff _).mp ht)

/-- No real constant approximates the optimum for global Greedy, with all
definitions stated using the maximal-string formulation of the source paper. -/
theorem paper_no_constant_approximation (C : Real) (N : Nat) :
    ∃ r, 10 ≤ r ∧ N ≤ (hardWord r).length ∧
      (∃ H steps, PaperGreedyRun (hardGrammar r) H steps ∧ PaperTerminal H) ∧
      ∀ H steps, PaperGreedyRun (hardGrammar r) H steps → PaperTerminal H →
        C < approximationRatio (hardWord r) H := by
  obtain ⟨r, hr, hn, hex, hall⟩ := no_constant_approximation C N
  refine ⟨r, hr, hn, ?_, ?_⟩
  · obtain ⟨H, steps, run, ht⟩ := hex
    exact ⟨H, steps, (paperGreedyRun_iff _ _ _).mpr run, (paperTerminal_iff _).mpr ht⟩
  · intro H steps run ht
    exact hall H steps ((paperGreedyRun_iff _ _ _).mp run) ((paperTerminal_iff _).mp ht)

end GreedyLowerBound
