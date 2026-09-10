import GreedyLowerBound.CountingLowerBound
import GreedyLowerBound.ComparisonSize

set_option autoImplicit false
namespace GreedyLowerBound

/-- The approximation-ratio estimate before division. Both grammar bounds
refer to the actual input and actual final Greedy grammar. -/
theorem input_ratio_cross (r : Nat) (hr : 10 ≤ r) (D : List Bool)
    (hD : D.length = (2^r)^2) (hU : UniqueWindows D (2*r))
    (H : Grammar) (steps : Nat) (run : GreedyRun (inputGrammar (2^r) D) H steps)
    (hterm : H.Terminal) :
    2^r * Grammar.minimumSize (inputWord (2^r) D) ≤ 4800*(H.size*(4*r+1)) := by
  have hh : 1 ≤ 2^r := Nat.one_le_pow _ _ (by decide)
  have hg := input_minimumSize_upper (2^r) D hh hD
  have hH := input_greedy_size_lower_power r hr D hD hU H steps run hterm
  calc
    _ ≤ 2^r*(600*(2^r)^2) := Nat.mul_le_mul_left (2^r) hg
    _ = 600*(2^r)^3 := by rw [Nat.pow_succ _ 2]; ac_rfl
    _ ≤ 600*(8*(H.size*(4*r+1))) := Nat.mul_le_mul_left 600 hH
    _ = _ := by rw [← Nat.mul_assoc]

end GreedyLowerBound
