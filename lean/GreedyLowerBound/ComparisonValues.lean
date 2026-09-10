import GreedyLowerBound.InputLength
import GreedyLowerBound.GrammarRecipe

set_option autoImplicit false
namespace GreedyLowerBound

/-- Finite morphism iteration starting from an arbitrary letter. -/
def muFrom : Nat → Letter → Word Letter
  | 0, c => [c]
  | u+1, c => muWord (muFrom u c)

theorem muFrom_zero_letter (u : Nat) : muFrom u 0 = muIterate u := by
  induction u with
  | zero => rfl
  | succ u ih => simp only [muFrom, muIterate, ih]

theorem muFrom_succ (u : Nat) (c : Letter) :
    muFrom (u+1) c = (mu c).flatMap (muFrom u) := by
  induction u with
  | zero => simp [muFrom, muWord]
  | succ u ih =>
    rw [muFrom, ih]
    simp only [muWord, List.flatMap_assoc, muFrom]

def comparisonAuxValue (j u : Nat) (c : Letter) : Word Nat :=
  (muFrom u c).flatMap (fun d => List.replicate (64^(j+1)) 0 ++ [markerName j d])

theorem comparisonAuxValue_zero (j : Nat) (c : Letter) :
    comparisonAuxValue j 0 c = List.replicate (64^(j+1)) 0 ++ [markerName j c] := by
  simp [comparisonAuxValue, muFrom]

theorem comparisonAuxValue_succ (j u : Nat) (c : Letter) :
    comparisonAuxValue j (u+1) c = (mu c).flatMap (comparisonAuxValue j u) := by
  rw [comparisonAuxValue, muFrom_succ, List.flatMap_assoc]
  rfl

theorem comparisonAuxValue_final (h j : Nat) :
    comparisonAuxValue j (auxiliaryExponent h (j+1)) 0 = inputAuxiliary h j := by
  rw [comparisonAuxValue, muFrom_zero_letter, inputAuxiliary_padded]
  simp only [paddedRuns, auxiliaryMarkers, List.flatMap_map]

def prefixValue (w : List Bool) (k : Nat) : Nat := binaryValue 64 (w.take k)

theorem prefixValue_zero (w : List Bool) : prefixValue w 0 = 0 := by
  simp [prefixValue, binaryValue]

theorem prefixValue_step (w : List Bool) (k : Nat) (hk : k < w.length) :
    prefixValue w (k+1) = 64*prefixValue w k + (if w[k] then 1 else 0) := by
  unfold prefixValue
  rw [List.take_succ_eq_append_getElem hk, binaryValue_append]
  simp [binaryValue, Nat.mul_comm]

theorem prefixValue_step_getD (w : List Bool) (k : Nat) (hk : k < w.length) :
    prefixValue w (k+1) = 64*prefixValue w k + (if w[k]?.getD false then 1 else 0) := by
  rw [prefixValue_step w k hk, List.getElem?_eq_getElem hk]
  rfl

/-- The unary expansion equation for a positive-prefix extension. -/
theorem unary_prefix_expansion (w : List Bool) (k : Nat) (hk : k < w.length) :
    List.replicate (prefixValue w (k+1)) 0 =
      (List.replicate 64 (List.replicate (prefixValue w k) 0)).flatten ++
      (if w[k]?.getD false then [0] else []) := by
  rw [prefixValue_step_getD w k hk, List.replicate_add, List.flatten_replicate_replicate]
  congr 1
  cases w[k]?.getD false <;> rfl

/-- The cost of a finite list bounds the cost of its set of rules, even if
a construction happens to list an index more than once. -/
theorem list_rule_cost_bound {ι : Type} [DecidableEq ι] (is : List ι) (cost : ι → Nat) :
    (∑ i ∈ is.toFinset, cost i) ≤ (is.map cost).sum := by
  induction is with
  | nil => simp
  | cons i is ih =>
    simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
    by_cases hi : i ∈ is.toFinset
    · rw [Finset.insert_eq_of_mem hi]
      omega
    · rw [Finset.sum_insert hi]
      omega

end GreedyLowerBound
