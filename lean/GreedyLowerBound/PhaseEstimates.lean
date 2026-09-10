import GreedyLowerBound.AuxiliaryRenaming
import GreedyLowerBound.Parameters
import GreedyLowerBound.UnaryScan

set_option autoImplicit false

namespace GreedyLowerBound

/-- Equation (15), for any base, with no enumeration of the possible d. -/
theorem shorter_unary_run_advantage (B d : Nat) (hd : 2 ≤ d) (hdB : d < B) :
    (B/d)*(d-1)+1 ≤ B-1 := by
  have hmod := Nat.mod_add_div B d
  have hr := Nat.mod_lt B (by omega : 0 < d)
  have hu : 1 ≤ B/d := (Nat.le_div_iff_mul_le (by omega)).mpr
    (by simpa only [Nat.one_mul] using Nat.le_of_lt hdB)
  have hsum : 2 ≤ B/d+B%d := by
    by_cases hu2 : 2 ≤ B/d
    · omega
    · have he : B/d = 1 := by omega
      rw [he, Nat.mul_one] at hmod
      omega
  have hmul : B/d*(d-1)+B/d = B/d*d := by
    calc
      _ = B/d*((d-1)+1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by congr 1; omega
  rw [Nat.mul_comm d (B/d)] at hmod
  omega

/-- Other runs divisible by B cannot favor a shorter unary factor. -/
theorem divisible_run_shorter_benefit (B d k : Nat) (hd : 2 ≤ d) (hdB : d ≤ B) :
    (k*B/d)*(d-1) ≤ k*(B-1) := by
  have hdpos : 0 < d := by omega
  have hu : k ≤ k*B/d := (Nat.le_div_iff_mul_le hdpos).mpr (Nat.mul_le_mul_left k hdB)
  have hcover : (k*B/d)*d ≤ k*B := Nat.div_mul_le_self (k*B) d
  have hmul : (k*B/d)*(d-1)+(k*B/d) = (k*B/d)*d := by
    calc
      _ = (k*B/d)*((d-1)+1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by congr 1; omega
  have hmulB : k*(B-1)+k = k*B := by
    calc
      _ = k*((B-1)+1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by congr 1; omega
  omega

theorem benchmark_gt_target_mass (h t : Nat) (hh : 1 ≤ h) (ht : t ≤ h) :
    (targetMass h : Int) < replacementGain (auxiliaryLength h t) 64 := by
  have hm := auxiliaryLength_gt_mass h t hh ht
  dsimp [replacementGain]
  omega

theorem benchmark_gt_long_unary_bound (h t : Nat) (hh : 1 ≤ h) (ht : t ≤ h) :
    (2*auxiliaryLength h t+targetMass h : Nat) < replacementGain (auxiliaryLength h t) 64 := by
  have hm := auxiliaryLength_gt_mass h t hh ht
  dsimp [replacementGain]
  simp only [Int.natCast_add, Int.natCast_mul]
  omega

theorem short_unary_gap_positive (h t : Nat) (hh : 1 ≤ h) (ht : t ≤ h) :
    (0 : Int) < (auxiliaryLength h t : Int)-(targetMass h : Int)-64 := by
  have hm := auxiliaryLength_gt_mass h t hh ht
  omega

/-- Equation (18), using only the weaker hypotheses M ≥ 32 and k ≥ 1.
The auxiliary run length is exactly 64*k. -/
theorem marker_bound_lt_unary_benchmark (M k : Nat) (hM : 32 ≤ M) (hk : 1 ≤ k)
    (gain : Int) (hgain : 16*gain ≤ (15*M*(64*k+1) : Nat)) :
    gain < replacementGain (M*k) 64 := by
  have hMk : M ≤ M*k := by simpa using Nat.mul_le_mul_left M hk
  have hMk' := Int.ofNat_le.mpr hMk
  simp only [Int.natCast_mul] at hMk' hgain
  dsimp [replacementGain]
  simp only [Int.natCast_mul]
  have hM' : (32 : Int) ≤ M := by omega
  have hk' : (1 : Int) ≤ k := by omega
  push_cast at hgain
  nlinarith

/-- Every marker-containing factor in an unfinished auxiliary loses strictly
to the local contribution of the intended base-64 substitution. -/
theorem auxiliary_marker_loses (h j k : Nat) (hh : 1 ≤ h)
    (hj : j ≤ h) (hk : 1 ≤ k)
    (f : Option Letter → Nat) (hf : Function.Injective f)
    (v : Word Nat) (c : Nat)
    (hp : Packing v ((auxiliaryWord (64*k) (muIterate (auxiliaryExponent h j))).map f) c)
    (hc : 2 ≤ c) (hm : ∃ a ∈ v, a ≠ f none) :
    replacementGain c v.length < replacementGain (auxiliaryLength h j*k) 64 := by
  have he : 2 ≤ auxiliaryExponent h j := by have := auxiliaryExponent_ge h j hj; omega
  have hb := auxiliary_gain_bound_renamed (auxiliaryExponent h j) (64*k) he f hf v c hp hc hm
  have hM : 32 ≤ auxiliaryLength h j := by have := auxiliaryLength_gt_mass h j hh hj; omega
  exact marker_bound_lt_unary_benchmark (auxiliaryLength h j) k hM hk _ hb

end GreedyLowerBound
