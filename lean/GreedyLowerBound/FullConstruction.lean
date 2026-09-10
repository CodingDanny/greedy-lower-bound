import GreedyLowerBound.CyclicSeed
import GreedyLowerBound.RatioArithmetic
import GreedyLowerBound.InputLength
import GreedyLowerBound.ExecutionExistence

set_option autoImplicit false
namespace GreedyLowerBound

/-- Choose a proved binary seed. All later conclusions hold for every seed
with the stated properties, so the particular choice is immaterial. -/
noncomputable def hardSeed (r : Nat) : List Bool :=
  if hr : 1 ≤ r then Classical.choose (lower_bound_cyclic_seed_exists r hr) else []

theorem hardSeed_spec (r : Nat) (hr : 1 ≤ r) :
    (hardSeed r).length = (2^r)^2 ∧ UniqueWindows (hardSeed r) (2*r) := by
  simpa only [hardSeed, dif_pos hr] using (show let D := Classical.choose (lower_bound_cyclic_seed_exists r hr);
      D.length = (2^r)^2 ∧ UniqueWindows D (2*r) from
      ⟨(Classical.choose_spec (lower_bound_cyclic_seed_exists r hr)).1,
       (Classical.choose_spec (lower_bound_cyclic_seed_exists r hr)).2.1⟩)

theorem hardSeed_cyclic (r : Nat) (hr : 1 ≤ r) : CyclicDeBruijn (hardSeed r) (2*r) := by
  simpa only [hardSeed, dif_pos hr] using
    (Classical.choose_spec (lower_bound_cyclic_seed_exists r hr)).2.2

noncomputable def hardWord (r : Nat) : Word Nat := inputWord (2^r) (hardSeed r)
noncomputable def hardGrammar (r : Nat) : Grammar := inputGrammar (2^r) (hardSeed r)

/-- The complete construction theorem over natural numbers, with no
unproved seed, phase, counting, or comparison-grammar premise. -/
theorem full_construction (r : Nat) (hr : 10 ≤ r) :
    (hardWord r).toFinset.card = (2^r)^2 + 4*(2^r) ∧
    (2^r)^2 + 4*(2^r) ≤ Grammar.minimumSize (hardWord r) ∧
    Grammar.minimumSize (hardWord r) ≤ 600*(2^r)^2 ∧
    2^(2^r) ≤ (hardWord r).length ∧
    (hardWord r).length ≤ 2^(50*(2^r)) ∧
    (∃ H steps, GreedyRun (hardGrammar r) H steps ∧ H.Terminal) ∧
    ∀ H steps, GreedyRun (hardGrammar r) H steps → H.Terminal →
      H.WellFormed ∧ H.Generates (hardWord r) ∧
      (2^r)^3 ≤ 8*(H.size*(4*r+1)) ∧
      2^r * Grammar.minimumSize (hardWord r) ≤ 4800*(H.size*(4*r+1)) := by
  obtain ⟨hD, hU⟩ := hardSeed_spec r (by omega)
  have hh : 1 ≤ 2^r := Nat.one_le_pow _ _ (by decide)
  refine ⟨inputWord_alphabet_card _ _ hh hD, input_minimumSize_lower _ _ hh hD,
    input_minimumSize_upper _ _ hh hD, inputWord_length_lower _ _ hh,
    inputWord_length_upper _ _ hh hD, ?_, ?_⟩
  · exact Grammar.terminal_run_exists _ (inputGrammar_wellFormed _ _ hh hD)
  · intro H steps run ht
    exact ⟨run.wellFormed (inputGrammar_wellFormed _ _ hh hD),
      run.preserves_word _ (inputGrammar_generates _ _),
      input_greedy_size_lower_power r hr _ hD hU H steps run ht,
      input_ratio_cross r hr _ hD hU H steps run ht⟩

/-- The family has arbitrarily large actual input lengths. -/
theorem hardWord_lengths_unbounded (N : Nat) :
    ∃ r, 10 ≤ r ∧ N ≤ (hardWord r).length := by
  let r := N+10
  have hr : 10 ≤ r := by omega
  have h₁ : r < 2^r := Nat.lt_two_pow_self
  have h₂ : 2^r < 2^(2^r) := Nat.lt_two_pow_self
  have hl := (full_construction r hr).2.2.2.1
  exact ⟨r, hr, by omega⟩

end GreedyLowerBound
