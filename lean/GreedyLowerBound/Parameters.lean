import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace GreedyLowerBound

def base : Nat := 64
def targetMass (h : Nat) : Nat := h^2*64^(2*h)
def auxiliaryExponent (h j : Nat) : Nat := 7*h+2-3*j
def auxiliaryLength (h j : Nat) : Nat := 19^(auxiliaryExponent h j)

theorem auxiliaryExponent_last (h : Nat) : auxiliaryExponent h h = 4*h+2 := by
  unfold auxiliaryExponent
  omega

theorem auxiliaryExponent_ge (h j : Nat) (hj : j ≤ h) :
    4*h+2 ≤ auxiliaryExponent h j := by unfold auxiliaryExponent; omega

theorem auxiliaryExponent_step (h j : Nat) (hj : j+1 ≤ h) :
    auxiliaryExponent h j = auxiliaryExponent h (j+1)+3 := by
  unfold auxiliaryExponent
  omega

theorem auxiliaryLength_step (h j : Nat) (hj : j+1 ≤ h) :
    auxiliaryLength h j = 6859*auxiliaryLength h (j+1) := by
  unfold auxiliaryLength
  rw [auxiliaryExponent_step h j hj, Nat.pow_add]
  change 19^auxiliaryExponent h (j+1)*6859 = 6859*19^auxiliaryExponent h (j+1)
  exact Nat.mul_comm _ _

theorem targetMass_le_two_pow (h : Nat) : targetMass h ≤ 2^(14*h) := by
  have hh : h ≤ 2^h := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hs := Nat.pow_le_pow_left hh 2
  unfold targetMass
  calc
    h^2*64^(2*h) ≤ (2^h)^2*64^(2*h) := Nat.mul_le_mul_right _ hs
    _ = (2^h)^2*(2^6)^(2*h) := by rfl
    _ = 2^(h*2+6*(2*h)) := by rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add]
    _ = 2^(14*h) := by congr 1; omega

theorem targetMass_ge_4096 (h : Nat) (hh : 1 ≤ h) : 4096 ≤ targetMass h := by
  have hh2 : 1 ≤ h^2 := Nat.one_le_pow _ _ hh
  have hp : 64^2 ≤ 64^(2*h) := Nat.pow_le_pow_right (by decide) (by omega)
  have hm := Nat.mul_le_mul hh2 hp
  simpa only [Nat.one_mul] using hm

theorem auxiliaryLength_last_gt_mass (h : Nat) (hh : 1 ≤ h) :
    1024*targetMass h < auxiliaryLength h h := by
  have hH := targetMass_le_two_pow h
  have hs : 1024*targetMass h ≤ 2^(16*h+8) := by
    calc
      1024*targetMass h ≤ 1024*2^(14*h) := Nat.mul_le_mul_left _ hH
      _ = 2^(10+14*h) := by rw [Nat.pow_add]
      _ ≤ 2^(16*h+8) := Nat.pow_le_pow_right (by decide) (by omega)
  have ht : 2^(16*h+8) < auxiliaryLength h h := by
    unfold auxiliaryLength
    rw [auxiliaryExponent_last]
    have hp := Nat.pow_lt_pow_left (a := 16) (b := 19) (n := 4*h+2) (by decide) (by omega)
    have he : (2^4)^(4*h+2) = 2^(16*h+8) := by rw [← Nat.pow_mul]; congr 1; omega
    simpa only [← he] using hp
  exact Nat.lt_of_le_of_lt hs ht

theorem auxiliaryLength_gt_mass (h j : Nat) (hh : 1 ≤ h) (hj : j ≤ h) :
    targetMass h+164 < auxiliaryLength h j := by
  have hlast := auxiliaryLength_last_gt_mass h hh
  have hH := targetMass_ge_4096 h hh
  have hexp := auxiliaryExponent_ge h j hj
  have hmono : auxiliaryLength h h ≤ auxiliaryLength h j := by
    unfold auxiliaryLength
    rw [auxiliaryExponent_last]
    exact Nat.pow_le_pow_right (by decide) hexp
  omega

/-- A finite geometric-tail estimate; it does not invoke an infinite series. -/
theorem finite_geometric_tail (a : Nat → Nat) (k : Nat)
    (ha : ∀ i, i < k → 64*a (i+1) ≤ a i) :
    63*(∑ i ∈ Finset.range k, a (i+1)) + a k ≤ a 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := ih (fun i hi => ha i (by omega))
    have ht := ha k (by omega)
    rw [Finset.sum_range_succ, Nat.mul_add]
    omega

def phaseWeight (h t s : Nat) : Nat := auxiliaryLength h (t+s)*64^(s+1)
def laterAuxiliaryMass (h t : Nat) : Nat :=
  ∑ s ∈ Finset.range (h-t), phaseWeight h t (s+1)

theorem phaseWeight_decay (h t s : Nat) (hts : t+s+1 ≤ h) :
    64*phaseWeight h t (s+1) ≤ phaseWeight h t s := by
  unfold phaseWeight
  have hm := auxiliaryLength_step h (t+s) hts
  have hi : t+(s+1) = t+s+1 := by omega
  rw [hi, hm, Nat.pow_succ]
  have hc : 4096 ≤ 6859 := by decide
  have hh := Nat.mul_le_mul_right (auxiliaryLength h (t+s+1)*64^(s+1)) hc
  calc
    _ = (64*64)*(auxiliaryLength h (t+s+1)*64^(s+1)) := by ac_rfl
    _ ≤ 6859*(auxiliaryLength h (t+s+1)*64^(s+1)) := hh
    _ = _ := by simp only [Nat.mul_assoc]

/-- Equation (17), in the slightly weaker strict form used to exclude long
active unary factors. The sum includes every later auxiliary. -/
theorem laterAuxiliaryMass_lt (h t : Nat) (ht : t ≤ h) :
    laterAuxiliaryMass h t < 2*auxiliaryLength h t := by
  have hh := finite_geometric_tail (phaseWeight h t) (h-t)
    (fun s hs => phaseWeight_decay h t s (by omega))
  have hm : 0 < auxiliaryLength h t := Nat.pow_pos (by decide)
  have h0 : phaseWeight h t 0 = 64*auxiliaryLength h t := by
    simp [phaseWeight, Nat.mul_comm]
  rw [h0] at hh
  change 63*laterAuxiliaryMass h t + phaseWeight h t (h-t) ≤
    64*auxiliaryLength h t at hh
  omega

end GreedyLowerBound
