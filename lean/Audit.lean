import GreedyLowerBound
import Lean.Util.CollectAxioms

/- This command inspects actual transitive dependencies in Lean's environment.
It is a build audit of actual proofs and final statements. The allowed axioms
are the standard Lean foundations. -/
open Lean Elab Command in
elab "#audit_greedy_declarations" : command => do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut theoremCount := 0
  for (name, info) in env.constants.toList do
    if (`GreedyLowerBound).isPrefixOf name then
      if info.isTheorem then
        theoremCount := theoremCount + 1
        let axioms ← collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Unapproved axiom {ax} in {name}"
  logInfo m!"Checked transitive axiom dependencies of {theoremCount} project theorems."
  logInfo "Allowed axioms: propext, Classical.choice, Quot.sound."
  for target in #[``GreedyLowerBound.full_lower_bound,
      ``GreedyLowerBound.greedy_logarithmic_lower_bound,
      ``GreedyLowerBound.no_constant_approximation,
      ``GreedyLowerBound.paper_greedy_logarithmic_lower_bound,
      ``GreedyLowerBound.paper_no_constant_approximation] do
    unless (env.find? target).any (fun info => info.isTheorem) do
      throwError "Required final theorem missing: {target}"
  logInfo "The complete lower-bound theorem and nonconstancy theorems are present and audited."

#audit_greedy_declarations
#print axioms GreedyLowerBound.muIterate_powerFree
#print axioms GreedyLowerBound.muIterate_spacing
#print axioms GreedyLowerBound.mu2_count_three
#print axioms GreedyLowerBound.scanCount_is_maximum
#print axioms GreedyLowerBound.Grammar.maximum_iff_maximal_maximum
#print axioms GreedyLowerBound.GreedyRun.rounds_bound
#print axioms GreedyLowerBound.GlobalStep.preserves_frozen_word
#print axioms GreedyLowerBound.GreedyRun.frozen_final_grammar
#print axioms GreedyLowerBound.Grammar.distinctFactors_card_le
#print axioms GreedyLowerBound.muIterate_short_count
#print axioms GreedyLowerBound.auxiliary_gain_bound_renamed
#print axioms GreedyLowerBound.Scan.unary_division_before_marker
#print axioms GreedyLowerBound.Scan.padded_word
#print axioms GreedyLowerBound.auxiliaryLength_gt_mass
#print axioms GreedyLowerBound.laterAuxiliaryMass_lt
#print axioms GreedyLowerBound.auxiliary_marker_loses
#print axioms GreedyLowerBound.GreedyRun.eligible_avoids_separator
#print axioms GreedyLowerBound.Fragmentation.frequency_eq
#print axioms GreedyLowerBound.ActiveStorage.unary_loses
#print axioms GreedyLowerBound.Fragmentation.auxiliary_marker_loses
#print axioms GreedyLowerBound.Scan.preserves_noAdjacent
#print axioms GreedyLowerBound.Fragmentation.afterStep_pieces
#print axioms GreedyLowerBound.ActiveStorage.afterCleanup
#print axioms GreedyLowerBound.binaryValue_digits
#print axioms GreedyLowerBound.targetState_advance
#print axioms GreedyLowerBound.targetState_no_other_unary
#print axioms GreedyLowerBound.Grammar.initial_generates
#print axioms GreedyLowerBound.GreedyRun.forces_event
#print axioms GreedyLowerBound.ActiveStorage.factor_in_target_loses
#print axioms GreedyLowerBound.targetNumbers_sum_le
#print axioms GreedyLowerBound.inputGrammar_wellFormed
#print axioms GreedyLowerBound.inputGrammar_generates
#print axioms GreedyLowerBound.initialActiveStorage
#print axioms GreedyLowerBound.input_first_step
#print axioms GreedyLowerBound.initialPhaseStorage
#print axioms GreedyLowerBound.PhaseStorage.protected_untouched
#print axioms GreedyLowerBound.PhaseStorage.cleanup_choice_exists
#print axioms GreedyLowerBound.PhaseStorage.cleanup_preserved
#print axioms GreedyLowerBound.PhaseStorage.forces_primary
#print axioms GreedyLowerBound.PhaseStorage.advance
#print axioms GreedyLowerBound.input_all_phases
#print axioms GreedyLowerBound.Grammar.semantics_exists
#print axioms GreedyLowerBound.Grammar.interpreted_distinctFactors_card_le
#print axioms GreedyLowerBound.input_factor_capacity
#print axioms GreedyLowerBound.Grammar.terminal_run_exists
#print axioms GreedyLowerBound.Grammar.minimumSize_attained
#print axioms GreedyLowerBound.input_minimumSize_lower
#print axioms GreedyLowerBound.encoded_factor_multiplicity
#print axioms GreedyLowerBound.target_lowerDigits_window
#print axioms GreedyLowerBound.equal_index_factors_reconstruct
#print axioms GreedyLowerBound.target_lowerDigits_length
#print axioms GreedyLowerBound.factorLength_le_quarter
#print axioms GreedyLowerBound.targetOccurrence_fiber_card_le_two
#print axioms GreedyLowerBound.targetDistinctFactors_lower
#print axioms GreedyLowerBound.input_greedy_size_lower_power
#print axioms GreedyLowerBound.inputWord_length_upper
#print axioms GreedyLowerBound.inputWord_length_lower
#print axioms GreedyLowerBound.comparisonRecipe
#print axioms GreedyLowerBound.comparisonGrammar_generates
#print axioms GreedyLowerBound.auxiliaryExponent_sum
#print axioms GreedyLowerBound.comparisonGrammar_size_bound
#print axioms GreedyLowerBound.input_minimumSize_upper
#print axioms GreedyLowerBound.input_ratio_cross

#print axioms GreedyLowerBound.Directed.eulerian_circuit
#print axioms GreedyLowerBound.BinaryOverlap.edge_tour_exists
#print axioms GreedyLowerBound.cyclic_deBruijn_exists
#print axioms GreedyLowerBound.hardSeed_spec
#print axioms GreedyLowerBound.hardSeed_cyclic
#print axioms GreedyLowerBound.dej_fixed_point
#print axioms GreedyLowerBound.dej_powerFree
#print axioms GreedyLowerBound.full_construction
#print axioms GreedyLowerBound.input_ratio_real
#print axioms GreedyLowerBound.full_lower_bound
#print axioms GreedyLowerBound.hardWord_lengths_infinite
#print axioms GreedyLowerBound.greedy_logarithmic_lower_bound
#print axioms GreedyLowerBound.no_constant_approximation
#print axioms GreedyLowerBound.paperGreedyRun_iff
#print axioms GreedyLowerBound.paperTerminal_iff
#print axioms GreedyLowerBound.paper_greedy_logarithmic_lower_bound
#print axioms GreedyLowerBound.paper_no_constant_approximation

#check GreedyLowerBound.full_lower_bound
#check GreedyLowerBound.paper_no_constant_approximation
