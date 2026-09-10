import GreedyLowerBound.ScanCount
import GreedyLowerBound.GrammarWellFormed
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace GreedyLowerBound

namespace Grammar

def frequency (G : Grammar) (v : Word Nat) : Nat :=
  ∑ i ∈ G.defined, scanCount v (G.rhs i)

def Eligible (G : Grammar) (v : Word Nat) : Prop :=
  2 ≤ v.length ∧ 2 ≤ G.frequency v

/-- Signed reduction, so the definition never silently truncates a negative
difference. All eligible candidates are proved to have nonnegative gain. -/
def gain (G : Grammar) (v : Word Nat) : Int :=
  (G.frequency v : Int) * ((v.length : Int) - 1) - (v.length : Int)

def Maximal (G : Grammar) (v : Word Nat) : Prop :=
  G.Eligible v ∧ ∀ u : Word Nat, v.length < u.length → G.frequency u < G.frequency v

theorem gain_nonnegative (G : Grammar) (v : Word Nat) (hv : G.Eligible v) :
    0 ≤ G.gain v := by
  rcases hv with ⟨hl, hc⟩
  have hl' : (2 : Int) ≤ v.length := by omega
  have hc' : (2 : Int) ≤ G.frequency v := by omega
  have hm := mul_nonneg (sub_nonneg.mpr hc') (sub_nonneg.mpr hl')
  dsimp [gain]
  nlinarith

theorem gain_strict_of_longer (G : Grammar) (v u : Word Nat) (hv : G.Eligible v)
    (hl : v.length < u.length) (hc : G.frequency v ≤ G.frequency u) :
    G.gain v < G.gain u := by
  rcases hv with ⟨hvlen, hvcount⟩
  have hl' : (v.length : Int) + 1 ≤ u.length := by omega
  have hc' : (G.frequency v : Int) ≤ G.frequency u := by omega
  have hvlen' : (2 : Int) ≤ v.length := by omega
  have hvcount' : (2 : Int) ≤ G.frequency v := by omega
  have hm1 := mul_nonneg (sub_nonneg.mpr hc')
    (show (0 : Int) ≤ (u.length : Int)-1 by omega)
  have hm2 := mul_nonneg (show (0 : Int) ≤ (G.frequency v : Int)-2 by omega)
    (show (0 : Int) ≤ (u.length : Int)-(v.length : Int)-1 by omega)
  dsimp [gain]
  nlinarith

theorem maximizing_is_maximal (G : Grammar) (v : Word Nat) (hv : G.Eligible v)
    (hm : ∀ u, G.Eligible u → G.gain u ≤ G.gain v) : G.Maximal v := by
  refine ⟨hv, ?_⟩
  intro u hlen
  by_contra hcount
  have hc : G.frequency v ≤ G.frequency u := by omega
  have hu : G.Eligible u := ⟨by have := hv.1; omega, by have := hv.2; omega⟩
  have hlt := G.gain_strict_of_longer v u hv hlen hc
  have hle := hm u hu
  omega

theorem card_le_size (G : Grammar) (hG : G.WellFormed) : G.defined.card ≤ G.size := by
  have hs : (∑ i ∈ G.defined, (1 : Nat)) ≤ G.size := by
    apply Finset.sum_le_sum
    intro i hi
    exact List.length_pos_iff.mpr (hG.2.1 i hi)
  simpa using hs

end Grammar

/-- The all-eligible-factor maximization formulation in Section 1 of the
manuscript. The equivalence to the original maximal-factor restriction has
two directions; `maximizing_is_maximal` establishes the immediate direction. -/
def GreedyStep (G H : Grammar) : Prop :=
  ∃ v : Word Nat, ∃ fresh : Nat,
    GlobalStep G H v fresh (fun i => scanCount v (G.rhs i)) ∧
    G.Eligible v ∧ (∀ u, G.Eligible u → G.gain u ≤ G.gain v)

namespace GreedyStep

variable {G H : Grammar}

theorem wellFormed (h : GreedyStep G H) (hG : G.WellFormed) : H.WellFormed := by
  rcases h with ⟨v, fresh, hr, he, _⟩
  apply hr.wellFormed hG
  intro hv
  have hh := he.1
  simp only [hv, List.length_nil] at hh
  omega

theorem size_le (h : GreedyStep G H) : H.size ≤ G.size := by
  rcases h with ⟨v, fresh, hr, he, _⟩
  have hv := he.1
  have hc := he.2
  have hsave := hr.size_accounting (by omega : 1 ≤ v.length)
  change H.size + G.frequency v * (v.length - 1) = G.size + v.length at hsave
  have hm : v.length ≤ G.frequency v * (v.length-1) := by
    have hx := Nat.mul_le_mul_right (v.length-1) hc
    omega
  omega

theorem card_eq (h : GreedyStep G H) : H.defined.card = G.defined.card + 1 := by
  rcases h with ⟨v, fresh, hr, _, _⟩
  rw [hr.domain, Finset.card_insert_of_not_mem hr.fresh_defined]

theorem preserves_word (h : GreedyStep G H) (w : Word Nat) (hw : G.Generates w) :
    H.Generates w := by
  rcases h with ⟨v, fresh, hr, _, _⟩
  exact hr.preserves_word w hw

end GreedyStep

inductive GreedyRun : Grammar → Grammar → Nat → Prop
  | nil (G : Grammar) : GreedyRun G G 0
  | cons {G H K : Grammar} {n : Nat} :
      GreedyStep G H → GreedyRun H K n → GreedyRun G K (n+1)

namespace GreedyRun

variable {G H : Grammar} {n : Nat}

theorem wellFormed (h : GreedyRun G H n) (hG : G.WellFormed) : H.WellFormed := by
  induction h with
  | nil => exact hG
  | cons hs ht ih => exact ih (hs.wellFormed hG)

theorem size_le (h : GreedyRun G H n) : H.size ≤ G.size := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons hs ht ih => exact Nat.le_trans ih hs.size_le

theorem card_eq (h : GreedyRun G H n) : H.defined.card = G.defined.card+n := by
  induction h with
  | nil => simp
  | cons hs ht ih => rw [ih, hs.card_eq]; omega

/-- Quantitative termination bound, including zero-gain steps. -/
theorem rounds_bound (h : GreedyRun G H n) (hG : G.WellFormed) :
    G.defined.card + n ≤ G.size := by
  have hcard := H.card_le_size (h.wellFormed hG)
  rw [h.card_eq] at hcard
  exact Nat.le_trans hcard h.size_le

theorem preserves_word (h : GreedyRun G H n) (w : Word Nat) (hw : G.Generates w) :
    H.Generates w := by
  induction h with
  | nil => exact hw
  | cons hs ht ih => exact ih (hs.preserves_word w hw)

end GreedyRun

end GreedyLowerBound
