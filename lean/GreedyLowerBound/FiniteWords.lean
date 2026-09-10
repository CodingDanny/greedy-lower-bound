import GreedyLowerBound.Words

set_option autoImplicit false

namespace GreedyLowerBound

universe u
variable {α : Type u} [DecidableEq α]

def equalIntervalsCheck (w : Word α) (a b r : Nat) : Bool :=
  (List.range r).all fun k => decide (w[a + k]? = w[b + k]?)

theorem equalIntervalsCheck_correct (w : Word α) (a b r : Nat) :
    equalIntervalsCheck w a b r = true ↔ EqualIntervals w a b r := by
  simp [equalIntervalsCheck, EqualIntervals, List.all_eq_true, List.mem_range]

/-- Exhaustive finite check of the shortest forbidden repetition for each
start and positive period. Longer forbidden repetitions contain one of these. -/
def powerFreeCheck (w : Word α) : Bool :=
  (List.range (w.length + 1)).all fun a =>
    (List.range (w.length + 1)).all fun d =>
      if 0 < d ∧ a + d + (3 * d / 4 + 1) ≤ w.length then
        !(equalIntervalsCheck w a (a + d) (3 * d / 4 + 1))
      else true

/-- Soundness of the finite computation, proved for arbitrary words.
This theorem is what connects a closed Boolean check to power-freeness. -/
theorem powerFreeCheck_sound (w : Word α) (hc : powerFreeCheck w = true) :
    PowerFree w := by
  apply (powerFree_iff_spaced w).mpr
  intro a d r hb hd he
  by_cases hs : 4 * r ≤ 3 * d
  · exact hs
  · have ha : a < w.length + 1 := by omega
    have hdb : d < w.length + 1 := by omega
    have hr : 3 * d / 4 + 1 ≤ r := by omega
    have hbound : a + d + (3 * d / 4 + 1) ≤ w.length := by omega
    have houter := List.all_eq_true.mp hc a (List.mem_range.mpr ha)
    have hinner := List.all_eq_true.mp houter d (List.mem_range.mpr hdb)
    have he' : EqualIntervals w a (a + d) (3 * d / 4 + 1) := by
      intro k hk
      exact he k (by omega)
    have ht := (equalIntervalsCheck_correct w a (a + d) (3 * d / 4 + 1)).mpr he'
    simp only [hd, hbound, and_self, if_true, ht, Bool.not_true] at hinner
    contradiction

/-- Completeness is useful for checking that the finite certificate has
exactly the conventional meaning rather than merely a sufficient test. -/
theorem powerFreeCheck_complete (w : Word α) (hg : PowerFree w) :
    powerFreeCheck w = true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro d hd
  split
  · next hb =>
      have hnot : ¬ EqualIntervals w a (a + d) (3 * d / 4 + 1) := by
        intro he
        have hs := occurrence_spacing w hg a d (3 * d / 4 + 1) hb.2 hb.1 he
        omega
      have hfalse : equalIntervalsCheck w a (a + d) (3 * d / 4 + 1) = false := by
        cases h : equalIntervalsCheck w a (a + d) (3 * d / 4 + 1) with
        | false => rfl
        | true => exact False.elim (hnot ((equalIntervalsCheck_correct _ _ _ _).mp h))
      simp [hfalse]
  · rfl

end GreedyLowerBound
