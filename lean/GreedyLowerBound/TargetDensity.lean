import GreedyLowerBound.DigitWindows

set_option autoImplicit false
namespace GreedyLowerBound

theorem slice_infix {α : Type} (w : Word α) (p L : Nat) : (slice w p L).IsInfix w := by
  refine ⟨w.take p, (w.drop p).drop L, ?_⟩
  simp only [slice, List.append_assoc, List.take_append_drop]

theorem slice_slice {α : Type} (w : Word α) (p L q K : Nat) (hb : q+K ≤ L) :
    slice (slice w p L) q K = slice w (p+q) K := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < K
  · rw [slice_get _ _ _ _ hk, slice_get _ _ _ _ (by omega), slice_get _ _ _ _ hk]
    rw [Nat.add_assoc]
  · simp only [slice, List.getElem?_take, hk, if_false]

theorem binaryEncode_slice (w : List Bool) (p L : Nat) :
    binaryEncode (slice w p L) = slice (binaryEncode w) (2*p) (2*L) := by
  unfold slice
  rw [binaryEncode_take, binaryEncode_drop]

theorem binaryEncode_count_true (w : List Bool) : (binaryEncode w).count true = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [binaryEncode, binaryCode, List.count_append] at * <;> omega

/-- Every encoded window contains at least floor(L/2)-1 complete codewords,
each contributing exactly one 1-bit. Both endpoint alignments are covered. -/
theorem encoded_window_ones (w : List Bool) (p L : Nat)
    (hb : p+L ≤ (binaryEncode w).length) :
    L/2-1 ≤ (slice (binaryEncode w) p L).count true := by
  by_cases hL : 2 ≤ L
  · let j := (p+1)/2
    let m := L/2-1
    let d := 2*j-p
    have hp : 2*j = p+d := by dsimp [j, d]; omega
    have hd : d+2*m ≤ L := by dsimp [d, j, m]; omega
    have hj : j+m ≤ w.length := by rw [binaryEncode_length] at hb; dsimp [j, m]; omega
    have hlen : (slice w j m).length = m := slice_length w j m hj
    have he : binaryEncode (slice w j m) = slice (slice (binaryEncode w) p L) d (2*m) := by
      rw [binaryEncode_slice, slice_slice _ _ _ _ _ hd, ← hp]
    have hc := (slice_infix (slice (binaryEncode w) p L) d (2*m)).count_le true
    rw [← he, binaryEncode_count_true, hlen] at hc
    exact hc
  · have he : L/2-1 = 0 := by omega
    rw [he]
    exact Nat.zero_le _

/-- The length estimate on every actual hard block in Section 6. -/
theorem target_lowerDigits_length (h : Nat) (D : List Bool) (s i : Nat)
    (hD : D.length = h^2) (hs : s < h) (hi : i < h) (A : Nat → Nat) :
    h/2-1 ≤ (lowerDigits (targetNumber h D s i) A h).length := by
  rw [target_lowerDigits_window h D s i hD hs hi A, List.length_map, oneIndices_length]
  apply encoded_window_ones
  change i+1+h ≤ (chunk h D s).length
  rw [chunk_length h D s hD hs]
  omega

/-- A uniform arithmetic estimate for all parameters in the manuscript. -/
theorem factorLength_le_quarter (r : Nat) (hr : 10 ≤ r) : 4*(4*r+2) ≤ 2^r := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hh : 10 ≤ r
    · have hp := ih hh
      rw [Nat.pow_succ]
      nlinarith
    · have he : r = 9 := by omega
      subst r
      decide

end GreedyLowerBound
