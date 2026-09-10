import GreedyLowerBound.AuxiliaryEncoding
import GreedyLowerBound.FactorCounts
import GreedyLowerBound.PackingSpacing

set_option autoImplicit false

namespace GreedyLowerBound

/-- The same signed reduction as `Grammar.gain`, with its occurrence count and
literal factor length made explicit. -/
def replacementGain (c n : Nat) : Int := (c : Int)*((n : Int)-1)-(n : Int)

theorem scaled_gain_le_of_benefit (c n bound : Nat) (hc : 1 ≤ c)
    (hb : 16*(c-1)*n ≤ bound) : 16*replacementGain c n ≤ (bound : Int) := by
  have he : ((c-1 : Nat) : Int) = (c : Int)-1 := by omega
  have hh := Int.ofNat_le.mpr hb
  simp only [Int.natCast_mul, he] at hh
  dsimp [replacementGain]
  nlinarith

theorem short_factor_coefficient (r : Nat) (hr : 1 ≤ r) (hr3 : r ≤ 3) :
    16*((if r = 1 then 121 else if r = 2 then 61 else 41)+r-1)*(r+1) ≤ 15*361 := by
  have he : r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases he with he | he | he <;> subst r <;> decide

/-- Lemma 2: every packing of a marker-containing factor in the padded
morphism iterate has gain at most `(15/16) * 19^e * (L+1)`. The integer form
clears the denominator and avoids any convention about truncated subtraction.
This covers every possible selection of disjoint occurrences. -/
theorem auxiliary_gain_bound (e L : Nat) (he : 2 ≤ e)
    (v : Word (Option Letter)) (c : Nat)
    (h : Packing v (auxiliaryWord L (muIterate e)) c)
    (hc : 2 ≤ c) (hm : markers v ≠ []) :
    16*replacementGain c v.length ≤ (15*19^e*(L+1) : Nat) := by
  let r := (markers v).length
  have hr : 1 ≤ r := List.length_pos_iff.mpr hm
  have hp := h.auxiliary_markers L (muIterate e) v c
  have hlen : v.length ≤ (r+1)*(L+1) :=
    Nat.le_of_lt (h.auxiliary_length_bound L (muIterate e) v c (by omega))
  apply scaled_gain_le_of_benefit c v.length _ (by omega)
  by_cases hr4 : 4 ≤ r
  · have hs := hp.spacing (markers v) (muIterate e) c hm (by omega) (muIterate_powerFree e)
    rw [muIterate_length] at hs
    have hcoef := large_marker_coefficient r (c-1) (19^e) hr4 hs
    calc
      16*(c-1)*v.length ≤ 16*(c-1)*((r+1)*(L+1)) := Nat.mul_le_mul_left _ hlen
      _ = (16*(c-1)*(r+1))*(L+1) := by simp only [Nat.mul_assoc]
      _ ≤ (15*19^e)*(L+1) := Nat.mul_le_mul_right _ hcoef
  · have hr3 : r ≤ 3 := by omega
    let m := if r = 1 then 121 else if r = 2 then 61 else 41
    have hcounts := muIterate_short_count (e-2) (markers v) hm hr3
    rw [show e-2+2 = e by omega] at hcounts
    have hpc := hp.count_le_factorCount hm
    have hcount : c ≤ 19^(e-2)*(m+r-1) := Nat.le_trans hpc hcounts
    have hcoef := short_factor_coefficient r hr hr3
    have hpow : 19^e = 19^(e-2)*361 := by
      calc
        19^e = 19^((e-2)+2) := congrArg (fun n => 19^n) (by omega)
        _ = 19^(e-2)*361 := by rw [Nat.pow_add]
    have hmul := Nat.mul_le_mul_right (19^(e-2)*(L+1)) hcoef
    calc
      16*(c-1)*v.length ≤ 16*c*v.length :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le c 1))
      _ ≤ 16*(19^(e-2)*(m+r-1))*((r+1)*(L+1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hcount) hlen
      _ ≤ 15*(19^(e-2)*361)*(L+1) := by
        simpa only [m, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
      _ = 15*19^e*(L+1) := by rw [hpow]

end GreedyLowerBound
