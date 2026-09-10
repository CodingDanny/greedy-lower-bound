import GreedyLowerBound.FullConstruction
import GreedyLowerBound.LogarithmicRatio

set_option autoImplicit false
namespace GreedyLowerBound

noncomputable def approximationRatio (w : Word Nat) (H : Grammar) : Real :=
  (H.size : Real) / Grammar.minimumSize w

/-- The full displayed theorem of Section 1, indexed by h = 2^r.
Every complete execution is covered, with arbitrary maximizing ties. -/
theorem full_lower_bound (r : Nat) (hr : 10 ≤ r) :
    (hardWord r).toFinset.card = (2^r)^2+4*(2^r) ∧
    (2^r)^2+4*(2^r) ≤ Grammar.minimumSize (hardWord r) ∧
    Grammar.minimumSize (hardWord r) ≤ 600*(2^r)^2 ∧
    2^(2^r) ≤ (hardWord r).length ∧
    (hardWord r).length ≤ 2^(50*(2^r)) ∧
    (∃ H steps, GreedyRun (hardGrammar r) H steps ∧ H.Terminal) ∧
    ∀ H steps, GreedyRun (hardGrammar r) H steps → H.Terminal →
      H.WellFormed ∧ H.Generates (hardWord r) ∧
      ((2 : Real)^r)^3 / (8*(4*(r : Real)+1)) ≤ H.size ∧
      (2 : Real)^r / (4800*(4*(r : Real)+1)) ≤ approximationRatio (hardWord r) H ∧
      Real.logb 2 ((hardWord r).length : Real) /
          (1200000 * Real.logb 2 (Real.logb 2 ((hardWord r).length : Real))) ≤
        (2 : Real)^r / (4800*(4*(r : Real)+1)) := by
  obtain ⟨ha, hglo, hghi, hnlo, hnhi, hex, hall⟩ := full_construction r hr
  refine ⟨ha, hglo, hghi, hnlo, hnhi, hex, ?_⟩
  intro H steps run ht
  obtain ⟨hw, hgen, hsize, hcross⟩ := hall H steps run ht
  obtain ⟨hD, hU⟩ := hardSeed_spec r (by omega)
  obtain ⟨h₁, h₂⟩ := input_ratio_real r hr (hardSeed r) hD hU H steps run ht
  refine ⟨hw, hgen, ?_, h₁, h₂⟩
  apply (div_le_iff₀ (show (0 : Real) < 8*(4*(r : Real)+1) by positivity)).mpr
  have hc : ((2 : Real)^r)^3 ≤ 8*((H.size : Real)*(4*(r : Real)+1)) := by
    exact_mod_cast hsize
  nlinarith [hc]

/-- Infinitely many distinct input lengths occur in the family. -/
theorem hardWord_lengths_infinite :
    Set.Infinite {n : Nat | ∃ r, 10 ≤ r ∧ n = (hardWord r).length} := by
  intro hf
  obtain ⟨M, hM⟩ := hf.bddAbove
  obtain ⟨r, hr, hn⟩ := hardWord_lengths_unbounded (M+1)
  have hh := hM (show (hardWord r).length ∈ {n : Nat | ∃ r, 10 ≤ r ∧ n = (hardWord r).length}
    from ⟨r, hr, rfl⟩)
  omega

/-- The logarithmic lower bound holds for arbitrarily large input lengths,
for every terminal execution on the chosen input. -/
theorem greedy_logarithmic_lower_bound (N : Nat) :
    ∃ r, 10 ≤ r ∧ N ≤ (hardWord r).length ∧
      (∃ H steps, GreedyRun (hardGrammar r) H steps ∧ H.Terminal) ∧
      ∀ H steps, GreedyRun (hardGrammar r) H steps → H.Terminal →
        Real.logb 2 ((hardWord r).length : Real) /
            (1200000 * Real.logb 2 (Real.logb 2 ((hardWord r).length : Real))) ≤
          approximationRatio (hardWord r) H := by
  obtain ⟨r, hr, hn⟩ := hardWord_lengths_unbounded N
  obtain ⟨_, _, _, _, _, hex, hall⟩ := full_lower_bound r hr
  refine ⟨r, hr, hn, hex, ?_⟩
  intro H steps run ht
  obtain ⟨_, _, _, h₁, h₂⟩ := hall H steps run ht
  exact h₂.trans h₁

/-- An elementary quantitative divergence bound for the family parameter. -/
theorem square_le_two_pow (r : Nat) (hr : 4 ≤ r) : r^2 ≤ 2^r := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hh : 4 ≤ r
    · have hp := ih hh
      rw [Nat.pow_succ 2 r]
      nlinarith
    · have he : r = 3 := by omega
      subst r
      decide

/-- Explicit nonconstancy, simultaneously with arbitrarily large lengths.
No limit theorem or asymptotic notation is needed to interpret this statement. -/
theorem greedy_ratio_unbounded (K N : Nat) :
    ∃ r, 10 ≤ r ∧ N ≤ (hardWord r).length ∧
      (∃ H steps, GreedyRun (hardGrammar r) H steps ∧ H.Terminal) ∧
      ∀ H steps, GreedyRun (hardGrammar r) H steps → H.Terminal →
        (K : Real) < approximationRatio (hardWord r) H := by
  obtain ⟨r, hrdef⟩ : ∃ r : Nat, r = 24000*(K+1)+N+10 := ⟨_, rfl⟩
  have hr : 10 ≤ r := by omega
  have hrK : 24000*(K+1) ≤ r := by omega
  have hs := square_le_two_pow r (by omega)
  have hd : 4800*(4*r+1) ≤ 24000*r := by omega
  have hc : (K+1)*(4800*(4*r+1)) ≤ 2^r := by
    have h₁ := Nat.mul_le_mul_left (K+1) hd
    have h₂ := Nat.mul_le_mul_right r hrK
    nlinarith [h₁, h₂, hs]
  obtain ⟨_, _, _, hnlo, _, hex, hall⟩ := full_lower_bound r hr
  have hn : N ≤ (hardWord r).length := by
    have h₁ : r < 2^r := Nat.lt_two_pow_self
    have h₂ : 2^r < 2^(2^r) := Nat.lt_two_pow_self
    omega
  refine ⟨r, hr, hn, hex, ?_⟩
  intro H steps run ht
  obtain ⟨_, _, _, hratio, _⟩ := hall H steps run ht
  have hcR : (K : Real)+1 ≤ (2 : Real)^r / (4800*(4*(r : Real)+1)) := by
    apply (le_div_iff₀ (show (0 : Real) < 4800*(4*(r : Real)+1) by positivity)).mpr
    exact_mod_cast hc
  linarith

/-- In particular, no real constant bounds the approximation ratio of this
algorithm on unrestricted alphabets, even after any finite length threshold. -/
theorem no_constant_approximation (C : Real) (N : Nat) :
    ∃ r, 10 ≤ r ∧ N ≤ (hardWord r).length ∧
      (∃ H steps, GreedyRun (hardGrammar r) H steps ∧ H.Terminal) ∧
      ∀ H steps, GreedyRun (hardGrammar r) H steps → H.Terminal →
        C < approximationRatio (hardWord r) H := by
  obtain ⟨K, hK⟩ := exists_nat_gt C
  obtain ⟨r, hr, hn, hex, hall⟩ := greedy_ratio_unbounded K N
  exact ⟨r, hr, hn, hex, fun H steps run ht => hK.trans (hall H steps run ht)⟩

end GreedyLowerBound
