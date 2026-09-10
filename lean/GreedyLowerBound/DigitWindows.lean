import GreedyLowerBound.BinaryWindows

set_option autoImplicit false
namespace GreedyLowerBound

/-- A prepended source bit does not alter lower base-64 digits. -/
theorem baseDigit_cons_lower (b : Bool) (w : List Bool) (u : Nat) (hu : u < w.length) :
    baseDigit (binaryValue 64 (b::w)) u = baseDigit (binaryValue 64 w) u := by
  have hpow : 64^w.length = 64^u * 64^(w.length-u) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hp : 0 < 64^u := Nat.pow_pos (by decide)
  have he : w.length-u = (w.length-u-1)+1 := by omega
  unfold baseDigit
  simp only [binaryValue]
  rw [hpow, ← Nat.mul_assoc, Nat.mul_comm (if b then 1 else 0) (64^u),
    Nat.mul_assoc, Nat.mul_add_div hp, Nat.add_mod]
  have hz : ((if b then 1 else 0)*64^(w.length-u)) % 64 = 0 := by
    rw [he, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_mod_left]
  rw [hz, Nat.zero_add, Nat.mod_mod]

theorem baseDigit_cons_top (b : Bool) (w : List Bool) :
    baseDigit (binaryValue 64 (b::w)) w.length = if b then 1 else 0 := by
  unfold baseDigit
  rw [binaryValue, Nat.mul_comm (if b then 1 else 0) (64^w.length),
    Nat.mul_add_div (Nat.pow_pos (by decide : 0 < 64)),
    Nat.div_eq_of_lt (binaryValue_lt 64 (by decide) w), Nat.add_zero]
  cases b <;> decide

/-- Exact digit/source-bit correspondence, with positions counted from the
right in the integer and from the left in the source word. -/
theorem baseDigit_binaryValue (w : List Bool) (u : Nat) (hu : u < w.length) :
    baseDigit (binaryValue 64 w) u = if w[w.length-1-u]? = some true then 1 else 0 := by
  induction w with
  | nil => simp at hu
  | cons b w ih =>
    by_cases ht : u < w.length
    · rw [baseDigit_cons_lower b w u ht, ih ht]
      have he : (b::w).length-1-u = (w.length-1-u)+1 := by simp only [List.length_cons]; omega
      rw [he, List.getElem?_cons_succ]
    · have he : u = w.length := by simp only [List.length_cons] at hu; omega
      subst u
      rw [baseDigit_cons_top]
      cases b <;> simp

/-- Lower digits depend only on the indicated suffix, including leading zero
bits within that suffix. -/
theorem lowerDigits_binaryValue_append (v w : List Bool) (A : Nat → Nat) (t : Nat)
    (ht : t ≤ w.length) :
    lowerDigits (binaryValue 64 (v++w)) A t = lowerDigits (binaryValue 64 w) A t := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    rw [List.cons_append, ← ih]
    have aux : ∀ k, k ≤ t →
        lowerDigits (binaryValue 64 (b::(v++w))) A k = lowerDigits (binaryValue 64 (v++w)) A k := by
      intro k
      induction k with
      | zero => intros; rfl
      | succ k ihk =>
        intro hk
        rw [lowerDigits, lowerDigits, baseDigit_cons_lower b (v++w) k (by simp; omega),
          ihk (by omega)]
    exact aux t (Nat.le_refl _)

/-- List of the primary indices selected by the 1-bits, in decreasing order. -/
def oneIndices : List Bool → List Nat
  | [] => []
  | b::w => (if b then [w.length] else []) ++ oneIndices w

theorem lowerDigits_binaryValue_full (w : List Bool) (A : Nat → Nat) :
    lowerDigits (binaryValue 64 w) A w.length = (oneIndices w).map A := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [List.length_cons, lowerDigits, baseDigit_cons_top]
    have ht := lowerDigits_binaryValue_append [b] w A w.length (Nat.le_refl _)
    simp only [List.singleton_append] at ht
    rw [ht, ih]
    cases b <;> simp [oneIndices]

theorem oneIndices_length (w : List Bool) : (oneIndices w).length = w.count true := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [oneIndices, ih]

/-- The post-phase hard block is exactly the selected primary-index list of
its underlying length-h binary window. -/
theorem target_lowerDigits_window (h : Nat) (D : List Bool) (s i : Nat)
    (hD : D.length = h^2) (hs : s < h) (hi : i < h) (A : Nat → Nat) :
    lowerDigits (targetNumber h D s i) A h =
      (oneIndices (slice (chunk h D s) (i+1) h)).map A := by
  let C := chunk h D s
  have hC : C.length = 2*h := chunk_length h D s hD hs
  have hlen : (C.take (h+1+i)).length = h+1+i := by simp [List.length_take, hC]; omega
  have hsplit : C.take (h+1+i) = (C.take (h+1+i)).take (i+1) ++
      (C.take (h+1+i)).drop (i+1) := (List.take_append_drop _ _).symm
  have htail : (C.take (h+1+i)).drop (i+1) = slice C (i+1) h := by
    rw [List.drop_take]
    have he : h+1+i-(i+1) = h := by omega
    rw [he]
    rfl
  have hwlen : (slice C (i+1) h).length = h := slice_length C (i+1) h (by omega)
  change lowerDigits (binaryValue 64 (C.take (h+1+i))) A h = _
  rw [hsplit, htail, lowerDigits_binaryValue_append _ _ A h (by rw [hwlen])]
  have he := lowerDigits_binaryValue_full (slice C (i+1) h) A
  rw [hwlen] at he
  exact he

end GreedyLowerBound
