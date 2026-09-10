import GreedyLowerBound.MorphismPowerFree
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace GreedyLowerBound

/-- Telescope the inequalities between consecutive occurrence positions. -/
theorem spacing_telescope (r : Nat) (pos : Nat → Nat) (k : Nat)
    (hs : ∀ i, i < k → 3*pos i + 4*r ≤ 3*pos (i+1)) :
    3*pos 0 + 4*r*k ≤ 3*pos k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (fun i hi => hs i (by omega))
    have hlast := hs k (by omega)
    rw [Nat.mul_succ]
    omega

/-- Lemma 1's many-occurrence estimate with denominators cleared. The indexed
positions are strictly increasing and all refer to one common factor. -/
theorem many_occurrences_spacing {α : Type} (w : Word α) (hg : PowerFree w)
    (r k : Nat) (pos : Nat → Nat)
    (hb : pos k+r ≤ w.length)
    (hinc : ∀ i, i < k → pos i < pos (i+1))
    (hbound : ∀ i, i ≤ k → pos i+r ≤ w.length)
    (he : ∀ i, i < k → EqualIntervals w (pos i) (pos (i+1)) r) :
    4*r*k + 3*r ≤ 3*w.length := by
  have hs : ∀ i, i < k → 3*pos i + 4*r ≤ 3*pos (i+1) := by
    intro i hi
    have hi' := hinc i hi
    have hb' := hbound (i+1) (by omega)
    have hspacing := occurrence_spacing w hg (pos i) (pos (i+1)-pos i) r
      (by omega) (by omega) (by
        have heq : pos i + (pos (i+1)-pos i) = pos (i+1) := by omega
        rw [heq]
        exact he i hi)
    omega
  have htel := spacing_telescope r pos k hs
  omega

/-- The `15/16` coefficient for factors with at least four markers. `k` is
one less than the number of occurrences. -/
theorem large_marker_coefficient (r k M : Nat) (hr : 4 ≤ r)
    (hs : 4*r*k + 3*r ≤ 3*M) : 16*k*(r+1) ≤ 15*M := by
  have hm := Nat.mul_le_mul_left k hr
  nlinarith

theorem short_marker_coefficients :
    16*242 < 15*361 ∧ 16*186 < 15*361 ∧ 16*172 < 15*361 := by decide

end GreedyLowerBound
