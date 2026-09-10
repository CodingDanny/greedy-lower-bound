import GreedyLowerBound.RatioArithmetic
import GreedyLowerBound.InputLength
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace GreedyLowerBound

/-- Change from the construction parameter to the actual input length. -/
theorem logarithmic_parameter_bounds (r n : Nat) (hr : 1 ≤ r)
    (hnl : 2^(2^r) ≤ n) (hnu : n ≤ 2^(50*(2^r))) :
    2^r ≤ Real.logb 2 (n : Real) ∧
    Real.logb 2 (n : Real) ≤ 50*(2 : Real)^r ∧
    (r : Real) ≤ Real.logb 2 (Real.logb 2 (n : Real)) := by
  have hb : (1 : Real) < 2 := by norm_num
  have hh : (0 : Real) < 2^r := by positivity
  have hlo : (2 : Real)^(2^r) ≤ (n : Real) := by exact_mod_cast hnl
  have hup : (n : Real) ≤ (2 : Real)^(50*(2^r)) := by exact_mod_cast hnu
  have hl := Real.logb_le_logb_of_le hb (by positivity : (0 : Real) < 2^(2^r)) hlo
  have hn : (0 : Real) < n := lt_of_lt_of_le (by positivity) hlo
  have hu := Real.logb_le_logb_of_le hb hn hup
  simp only [Real.logb_pow, Real.logb_self_eq_one hb, mul_one, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_mul] at hl hu
  have hll := Real.logb_le_logb_of_le hb hh hl
  simp only [Real.logb_pow, Real.logb_self_eq_one hb, mul_one] at hll
  exact ⟨hl, hu, hll⟩

/-- Both displayed approximation-ratio inequalities, with base-two logs.
The seed property is the only construction premise at this stage. -/
theorem input_ratio_real (r : Nat) (hr : 10 ≤ r) (D : List Bool)
    (hD : D.length = (2^r)^2) (hU : UniqueWindows D (2*r))
    (H : Grammar) (steps : Nat) (run : GreedyRun (inputGrammar (2^r) D) H steps)
    (hterm : H.Terminal) :
    (2 : Real)^r / (4800*(4*(r : Real)+1)) ≤
      (H.size : Real) / Grammar.minimumSize (inputWord (2^r) D) ∧
    Real.logb 2 ((inputWord (2^r) D).length : Real) /
        (1200000 * Real.logb 2 (Real.logb 2 ((inputWord (2^r) D).length : Real))) ≤
      (2 : Real)^r / (4800*(4*(r : Real)+1)) := by
  have hh : 1 ≤ 2^r := Nat.one_le_pow _ _ (by decide)
  have hg : (0 : Real) < Grammar.minimumSize (inputWord (2^r) D) := by
    exact_mod_cast Grammar.minimumSize_pos _ (inputWord_nonempty (2^r) D hh hD)
  have hd : (0 : Real) < 4800*(4*(r : Real)+1) := by positivity
  have hc : (2 : Real)^r * Grammar.minimumSize (inputWord (2^r) D) ≤
      4800*((H.size : Real)*(4*(r : Real)+1)) := by
    exact_mod_cast input_ratio_cross r hr D hD hU H steps run hterm
  constructor
  · apply (div_le_div_iff₀ hd hg).mpr
    nlinarith [hc]
  · obtain ⟨hl, hu, hll⟩ := logarithmic_parameter_bounds r (inputWord (2^r) D).length
      (by omega) (inputWord_length_lower _ D hh) (inputWord_length_upper _ D hh hD)
    have hrR : (1 : Real) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    have hlog : (0 : Real) < Real.logb 2 (Real.logb 2 ((inputWord (2^r) D).length : Real)) := by
      linarith
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hlog) hd).mpr
    have h₁ := mul_le_mul_of_nonneg_right hu (le_of_lt hd)
    have h₂ := mul_le_mul_of_nonneg_left hll (show (0 : Real) ≤ 1200000*2^r by positivity)
    have h₃ : (4*(r : Real)+1) ≤ 5*r := by linarith
    have h₄ := mul_le_mul_of_nonneg_left h₃ (show (0 : Real) ≤ 240000*2^r by positivity)
    nlinarith [h₁, h₂, h₄]

end GreedyLowerBound
