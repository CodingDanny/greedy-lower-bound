import GreedyLowerBound.ScanCount

set_option autoImplicit false

namespace GreedyLowerBound

universe u
variable {α : Type u}

/-- A choice of disjoint occurrences, in their order in the input. Each `next`
consumes an arbitrary prefix and then one whole copy of the factor. -/
inductive Packing (v : Word α) : Word α → Nat → Prop
  | zero (s : Word α) : Packing v s 0
  | next (pre rest : Word α) {c : Nat} :
      Packing v rest c → Packing v (pre ++ (v ++ rest)) (c+1)

namespace Packing

variable {v s : Word α} {c : Nat}

theorem prepend (h : Packing v s c) (p : Word α) : Packing v (p++s) c := by
  cases h with
  | zero s => exact Packing.zero _
  | next pre rest ht =>
    simpa only [List.append_assoc] using Packing.next (p++pre) rest ht

/-- Cutting at most one factor-length from the front discards at most the
first chosen occurrence. This is the exchange step for equal-length intervals. -/
theorem drop_short (h : Packing v s (c+1)) (k : Nat) (hk : k ≤ v.length) :
    Packing v (s.drop k) c := by
  cases h with
  | next pre rest ht =>
    have hle : k ≤ (pre++v).length := by simp only [List.length_append]; omega
    rw [← List.append_assoc, List.drop_append_of_le_length hle]
    exact ht.prepend ((pre++v).drop k)

theorem drop_one_of_not_prefix (h : Packing v s c) (hn : ¬ v.IsPrefix s) :
    Packing v (s.drop 1) c := by
  cases h with
  | zero s => exact Packing.zero _
  | next pre rest ht =>
    cases pre with
    | nil => exact False.elim (hn (by simp))
    | cons a pre =>
      simpa only [List.cons_append, List.drop_succ_cons, List.drop_zero] using
        Packing.next pre rest ht

theorem factor_length_le (h : Packing v s c) (hc : 0 < c) : v.length ≤ s.length := by
  cases h with
  | zero => omega
  | next pre rest ht => simp only [List.length_append]; omega

end Packing

namespace Scan

variable {v s t : Word α} {fresh : α} {c : Nat}

theorem packing (h : Scan v fresh s t c) : Packing v s c := by
  induction h with
  | nil => exact Packing.zero _
  | hit h ih => exact Packing.next [] _ ih
  | @skip a s t c hn h ih => exact ih.prepend [a]

/-- Leftmost selection is optimal over every disjoint occurrence choice. -/
theorem maximum (h : Scan v fresh s t c) (hv : v ≠ [])
    (k : Nat) (hk : Packing v s k) : k ≤ c := by
  induction h generalizing k with
  | nil =>
    by_cases hk0 : k = 0
    · omega
    · have hh := hk.factor_length_le (by omega : 0 < k)
      have hvlen := List.length_pos_iff.mpr hv
      simp only [List.length_nil] at hh
      omega
  | @hit s t c h ih =>
    cases k with
    | zero => omega
    | succ k =>
      have hd := hk.drop_short v.length (Nat.le_refl _)
      rw [List.drop_left] at hd
      have hh := ih k hd
      omega
  | @skip a s t c hn h ih =>
    have hd := hk.drop_one_of_not_prefix hn
    simpa only [List.drop_succ_cons, List.drop_zero] using ih k hd

end Scan

/-- Exact characterization of the maximum count, including attainment. -/
theorem scanCount_is_maximum [DecidableEq α] (v s : Word α) (hv : v ≠ []) :
    Packing v s (scanCount v s) ∧ ∀ k, Packing v s k → k ≤ scanCount v s := by
  cases v with
  | nil => exact False.elim (hv rfl)
  | cons a v =>
    obtain ⟨t, ht⟩ := Scan.exists_output (a::v) s a hv
    exact ⟨ht.packing, ht.maximum hv⟩

end GreedyLowerBound
