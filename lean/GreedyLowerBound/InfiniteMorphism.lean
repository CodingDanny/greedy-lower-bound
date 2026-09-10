import GreedyLowerBound.MorphismPowerFree
import Mathlib.Data.List.Infix

set_option autoImplicit false
namespace GreedyLowerBound

theorem muIterate_prefix_succ (e : Nat) : muIterate e <+: muIterate (e+1) := by
  induction e with
  | zero => decide
  | succ e ih => exact ih.flatMap mu

theorem muIterate_prefix (e f : Nat) (hef : e ≤ f) : muIterate e <+: muIterate f := by
  induction f with
  | zero =>
    have he : e = 0 := by omega
    subst e
    exact ⟨[], by simp⟩
  | succ f ih =>
    by_cases he : e ≤ f
    · exact (ih he).trans (muIterate_prefix_succ f)
    · have he : e = f+1 := by omega
      subst e
      exact ⟨[], by simp⟩

theorem iterate_index_bound (i : Nat) : i < (muIterate (i+1)).length := by
  rw [muIterate_length]
  have h : i+1 < 19^(i+1) := Nat.lt_pow_self (by decide)
  omega

/-- The infinite word defined by the nested finite iterates. -/
def dej (i : Nat) : Letter := (muIterate (i+1))[i]'(iterate_index_bound i)

/-- Every sufficiently long finite iterate gives exactly the same letter. -/
theorem dej_eq_iterate (e i : Nat) (hi : i < (muIterate e).length) :
    dej i = (muIterate e)[i]'hi := by
  unfold dej
  rcases le_total (i+1) e with he | he
  · exact (muIterate_prefix (i+1) e he).getElem (iterate_index_bound i)
  · exact ((muIterate_prefix e (i+1) he).getElem hi).symm

/-- The infinite limit has precisely the same strict power-freeness property. -/
theorem dej_powerFree (a L p : Nat) (hp : 0 < p)
    (hper : ∀ k, k+p < L → dej (a+k) = dej (a+k+p)) : 4*L ≤ 7*p := by
  let e := a+L+1
  have hb : a+L < (muIterate e).length := by
    rw [muIterate_length]
    have h : e < 19^e := Nat.lt_pow_self (by decide)
    dsimp [e] at h ⊢
    omega
  apply muIterate_powerFree e a L p (by omega) hp
  intro k hk
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
  exact congrArg some ((dej_eq_iterate e (a+k) (by omega)).symm.trans
    ((hper k hk).trans (dej_eq_iterate e (a+k+p) (by omega))))

/-- Applying the 19-uniform morphism to the infinite word fixes it. -/
theorem dej_fixed_point (i o : Nat) (ho : o < 19) :
    some (dej (19*i+o)) = (mu (dej i))[o]? := by
  let e := i+1
  have hi : i < (muIterate e).length := iterate_index_bound i
  have hio : 19*i+o < (muIterate (e+1)).length := by
    rw [muIterate, muWord_length]
    omega
  rw [dej_eq_iterate (e+1) (19*i+o) hio, dej_eq_iterate e i hi]
  have hh := muWord_get (muIterate e) i o hi ho
  change (muIterate (e+1))[19*i+o]? = (mu (muIterate e)[i])[o]? at hh
  rwa [List.getElem?_eq_getElem hio] at hh

end GreedyLowerBound
