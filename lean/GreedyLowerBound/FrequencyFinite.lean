import GreedyLowerBound.MorphismFinite

set_option autoImplicit false

namespace GreedyLowerBound

/-- Literal overlapping occurrence count, obtained by checking each suffix.
A prefix test succeeds only if the entire factor fits. The empty factor has
the conventional `length + 1` occurrences. -/
def factorCount (w v : Word Letter) : Nat :=
  match w with
  | [] => if v = [] then 1 else 0
  | a :: w => (if v.IsPrefix (a :: w) then 1 else 0) + factorCount w v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mu2_count_one : ∀ a b : Letter,
    factorCount (muWord (mu a)) [b] ≤ 121 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mu2_count_two : ∀ a b c : Letter,
    factorCount (muWord (mu a)) [b,c] ≤ 61 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mu2_count_three : ∀ a b c d : Letter,
    factorCount (muWord (mu a)) [b,c,d] ≤ 41 := by decide

end GreedyLowerBound
