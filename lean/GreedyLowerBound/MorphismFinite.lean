import GreedyLowerBound.FiniteWords

set_option autoImplicit false

namespace GreedyLowerBound

abbrev Letter := Fin 3

/-- The exact three images in equation (2) of the manuscript. -/
def mu (c : Letter) : Word Letter :=
  if c = 0 then
    [0,1,2,0,2,1,2,0,1,2,1,0,2,1,2,0,2,1,0]
  else if c = 1 then
    [1,2,0,1,0,2,0,1,2,0,2,1,0,2,0,1,0,2,1]
  else
    [2,0,1,2,1,0,1,2,0,1,0,2,1,0,1,2,1,0,2]

def muWord (w : Word Letter) : Word Letter := w.flatMap mu

theorem mu_length (c : Letter) : (mu c).length = 19 := by
  by_cases h0 : c = 0
  · simp [mu, h0]
  · by_cases h1 : c = 1 <;> simp [mu, h0, h1]

theorem muWord_length (w : Word Letter) : (muWord w).length = 19 * w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp only [muWord, List.flatMap_cons, List.length_append, List.length_cons,
        mu_length] at *
      omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mu_single_checks : ∀ a : Letter, powerFreeCheck (muWord [a]) = true := by
  decide

theorem mu_single_powerFree (a : Letter) : PowerFree (muWord [a]) :=
  powerFreeCheck_sound _ (mu_single_checks a)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mu_pair_checks : ∀ a b : Letter, a ≠ b →
    powerFreeCheck (muWord [a,b]) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mu_triple_checks : ∀ a b c : Letter, a ≠ b → b ≠ c →
    powerFreeCheck (muWord [a,b,c]) = true := by
  decide

theorem mu_pair_powerFree (a b : Letter) (hab : a ≠ b) :
    PowerFree (muWord [a,b]) := powerFreeCheck_sound _ (mu_pair_checks a b hab)

theorem mu_triple_powerFree (a b c : Letter) (hab : a ≠ b) (hbc : b ≠ c) :
    PowerFree (muWord [a,b,c]) := powerFreeCheck_sound _ (mu_triple_checks a b c hab hbc)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- All six rows and all six columns of Table A.1, including crossing starts.
`t = 0` is a prefix and `t = 1` is a suffix. -/
theorem mu_synchronization_table : ∀ a b c : Letter, a ≠ b →
    ∀ i : Fin 19, ∀ t : Fin 2,
      ((mu a ++ mu b).drop i.val).take 7 = ((mu c).drop (12 * t.val)).take 7 →
      i.val = 12 * t.val ∧ a = c := by
  decide

theorem mu_endpoints : ∀ a : Letter, (mu a)[0]? = some a ∧
    (mu a)[18]? = some a := by decide

/-- Appendix A.2 in its arbitrary-word form. Exhaustion is over the actual
three-letter alphabet, so a cyclic-renaming lemma is unnecessary. -/
theorem mu_short_powerFree (w : Word Letter) (hg : PowerFree w) (hl : w.length ≤ 3) :
    PowerFree (muWord w) := by
  cases w with
  | nil => exact PowerFree.of_length_le_one [] (by decide)
  | cons a w =>
    cases w with
    | nil => exact mu_single_powerFree a
    | cons b w =>
      have hab : a ≠ b := by
        have hh := hg.no_equal_neighbors 0 (by simp)
        simpa using hh
      cases w with
      | nil => exact mu_pair_powerFree a b hab
      | cons c w =>
        have hbc : b ≠ c := by
          have hh := hg.no_equal_neighbors 1 (by simp)
          simpa using hh
        have hw : w = [] := by simpa using hl
        subst w
        exact mu_triple_powerFree a b c hab hbc

end GreedyLowerBound
