import GreedyLowerBound.ComparisonValues
import Mathlib.Data.Nat.Pairing

set_option autoImplicit false
namespace GreedyLowerBound

inductive ComparisonIndex
  | target (s k : Nat)
  | power (j : Nat)
  | aux (j u : Nat) (c : Letter)
  | start
  deriving DecidableEq

namespace ComparisonIndex

def code : ComparisonIndex → Nat
  | .target s k => Nat.pair 0 (Nat.pair s k)
  | .power j => Nat.pair 1 j
  | .aux j u c => Nat.pair 2 (Nat.pair j (Nat.pair u c.val))
  | .start => Nat.pair 3 0

theorem code_injective : Function.Injective code := by
  intro a b he
  cases a <;> cases b <;> simp_all [code, Nat.pair_eq_pair, Fin.ext_iff]

end ComparisonIndex

open ComparisonIndex

def comparisonTargets (h : Nat) (D : List Bool) : List ComparisonIndex :=
  (List.range h).flatMap (fun s => ((List.range (2*h)).filter
    (fun k => decide (0 < prefixValue (chunk h D s) (k+1)))).map (target s))

def comparisonPowers (h : Nat) : List ComparisonIndex := (List.range h).map power

def comparisonAuxiliaries (h : Nat) : List ComparisonIndex :=
  (List.range h).flatMap (fun j => (List.range (auxiliaryExponent h (j+1)+1)).flatMap
    (fun u => (List.finRange 3).map (aux j u)))

def comparisonIndices (h : Nat) (D : List Bool) : List ComparisonIndex :=
  comparisonTargets h D ++ comparisonPowers h ++ comparisonAuxiliaries h ++ [start]

def ComparisonValid (h : Nat) (D : List Bool) : ComparisonIndex → Prop
  | .target s k => s < h ∧ k < 2*h ∧ 0 < prefixValue (chunk h D s) (k+1)
  | .power j => j < h
  | .aux j u _ => j < h ∧ u ≤ auxiliaryExponent h (j+1)
  | .start => True

/-- Exactly the positive prefix rules are included. No empty prefix is
silently represented by an empty production. -/
theorem mem_comparisonIndices (h : Nat) (D : List Bool) (x : ComparisonIndex) :
    x ∈ comparisonIndices h D ↔ ComparisonValid h D x := by
  cases x <;> simp [comparisonIndices, comparisonTargets, comparisonPowers,
    comparisonAuxiliaries, ComparisonValid, and_assoc, Nat.lt_succ_iff]

end GreedyLowerBound
