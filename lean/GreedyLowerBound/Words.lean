import Lean

set_option autoImplicit false

namespace GreedyLowerBound

universe u

abbrev Word (α : Type u) := List α

variable {α : Type u}

/-- Equality of two length-`r` intervals, expressed without arbitrary default letters.
The callers supply the interval bounds separately. -/
def EqualIntervals (w : Word α) (a b r : Nat) : Prop :=
  ∀ k, k < r → w[a + k]? = w[b + k]?

/-- Period `p` of the length-`L` factor starting at `a`. -/
def PeriodAt (w : Word α) (a L p : Nat) : Prop :=
  ∀ k, k + p < L → w[a + k]? = w[a + k + p]?

/-- The conventional strict `(7/4)^+`-free property, for every positive period.
All positions and lengths refer to literal letters of the word. -/
def PowerFree (w : Word α) : Prop :=
  ∀ a L p, a + L ≤ w.length → 0 < p → PeriodAt w a L p → 4 * L ≤ 7 * p

/-- The equivalent spacing formulation used by the auxiliary-word estimates. -/
def Spaced (w : Word α) : Prop :=
  ∀ a d r, a + d + r ≤ w.length → 0 < d →
    EqualIntervals w a (a + d) r → 4 * r ≤ 3 * d

theorem powerFree_iff_spaced (w : Word α) : PowerFree w ↔ Spaced w := by
  constructor
  · intro hg a d r hb hd he
    have hp : PeriodAt w a (d + r) d := by
      intro k hk
      have hkr : k < r := by omega
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he k hkr
    have h := hg a (d + r) d (by omega) hd hp
    omega
  · intro hs a L p hb hp he
    by_cases hLp : L ≤ p
    · omega
    · have heq : EqualIntervals w a (a + p) (L - p) := by
        intro k hk
        have hkL : k + p < L := by omega
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he k hkL
      have h := hs a p (L - p) (by omega) hp heq
      omega

/-- Lemma 1's two-occurrence inequality, with integer denominators cleared. -/
theorem occurrence_spacing (w : Word α) (hg : PowerFree w)
    (a d r : Nat) (hb : a + d + r ≤ w.length) (hd : 0 < d)
    (he : EqualIntervals w a (a + d) r) : 4 * r ≤ 3 * d :=
  (powerFree_iff_spaced w).mp hg a d r hb hd he

namespace PowerFree

theorem of_length_le_one (w : Word α) (hw : w.length ≤ 1) : PowerFree w := by
  intro a L p hb hp _
  omega

/-- Restriction to a literal interval preserves power-freeness. -/
theorem interval {w z : Word α} (hg : PowerFree w) (off : Nat)
    (hb : off + z.length ≤ w.length)
    (he : ∀ i, i < z.length → z[i]? = w[off + i]?) : PowerFree z := by
  intro a L p ha hp hper
  apply hg (off + a) L p (by omega) hp
  intro k hk
  have h := hper k hk
  rw [he (a + k) (by omega), he (a + k + p) (by omega)] at h
  simpa only [Nat.add_assoc] using h

theorem no_equal_neighbors {w : Word α} (hg : PowerFree w) (i : Nat)
    (hi : i + 1 < w.length) : w[i]? ≠ w[i+1]? := by
  intro he
  have hper : PeriodAt w i 2 1 := by
    intro k hk
    have hk0 : k = 0 := by omega
    simpa only [hk0, Nat.add_zero] using he
  have h := hg i 2 1 (by omega) (by decide) hper
  omega

theorem drop {w : Word α} (hg : PowerFree w) (n : Nat) : PowerFree (w.drop n) := by
  by_cases hn : n ≤ w.length
  · apply hg.interval n
    · simp only [List.length_drop]; omega
    · intro i _; exact List.getElem?_drop
  · have he : w.drop n = [] := List.drop_eq_nil_of_le (by omega)
    rw [he]
    exact of_length_le_one [] (by simp)

theorem take {w : Word α} (hg : PowerFree w) (n : Nat) : PowerFree (w.take n) := by
  apply hg.interval 0
  · simp only [Nat.zero_add, List.length_take]; omega
  · intro i hi
    have hin : i < n := by simp only [List.length_take] at hi; omega
    simpa only [Nat.zero_add] using (List.getElem?_take_of_lt hin : (w.take n)[i]? = w[i]?)

end PowerFree

end GreedyLowerBound
