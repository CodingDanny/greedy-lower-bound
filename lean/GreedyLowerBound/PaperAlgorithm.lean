import GreedyLowerBound.MaximalFactors
import GreedyLowerBound.InitialGrammar

set_option autoImplicit false
namespace GreedyLowerBound

/-- Section VI.D/F of The Smallest Grammar Problem: maximize the reduction
among maximal repeated strings, then scan every old production left to right. -/
def PaperGreedyStep (G H : Grammar) : Prop :=
  ∃ v : Word Nat, ∃ fresh : Nat,
    GlobalStep G H v fresh (fun i => scanCount v (G.rhs i)) ∧
    G.Maximal v ∧ (∀ u, G.Maximal u → G.gain u ≤ G.gain v)

theorem paperGreedyStep_iff (G H : Grammar) : PaperGreedyStep G H ↔ GreedyStep G H := by
  unfold PaperGreedyStep GreedyStep
  simp only [Grammar.maximum_iff_maximal_maximum]

inductive PaperGreedyRun : Grammar → Grammar → Nat → Prop
  | nil (G : Grammar) : PaperGreedyRun G G 0
  | cons {G H K : Grammar} {n : Nat} :
      PaperGreedyStep G H → PaperGreedyRun H K n → PaperGreedyRun G K (n+1)

theorem paperGreedyRun_iff (G H : Grammar) (n : Nat) :
    PaperGreedyRun G H n ↔ GreedyRun G H n := by
  constructor
  · intro run
    induction run with
    | nil G => exact GreedyRun.nil G
    | cons step run ih => exact GreedyRun.cons ((paperGreedyStep_iff _ _).mp step) ih
  · intro run
    induction run with
    | nil G => exact PaperGreedyRun.nil G
    | cons step run ih => exact PaperGreedyRun.cons ((paperGreedyStep_iff _ _).mpr step) ih

def PaperTerminal (G : Grammar) : Prop := ∀ v, ¬ G.Maximal v

theorem paperTerminal_iff (G : Grammar) : PaperTerminal G ↔ G.Terminal := by
  constructor
  · intro ht v hv
    obtain ⟨u, hu, _⟩ := G.eligible_dominated_by_maximal v hv
    exact ht u hu
  · intro ht v hv
    exact ht v hv.1

end GreedyLowerBound
