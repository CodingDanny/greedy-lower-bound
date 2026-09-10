import GreedyLowerBound.FrequencyFinite
import GreedyLowerBound.MorphismPowerFree
import GreedyLowerBound.MaximumOccurrences
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace GreedyLowerBound

theorem factorCount_zero_of_short (w v : Word Letter) (h : w.length < v.length) :
    factorCount w v = 0 := by
  induction w with
  | nil =>
    have hv : v ≠ [] := by intro he; simp only [he, List.length_nil] at h; omega
    simp [factorCount, hv]
  | cons a w ih =>
    have hp : ¬ v.IsPrefix (a::w) := by intro hp; have := hp.length_le; omega
    have ht : w.length < v.length := by simp only [List.length_cons] at h; omega
    simp only [factorCount, if_neg hp, Nat.zero_add, ih ht]

theorem factorCount_prepend_le (pre w v : Word Letter) :
    factorCount w v ≤ factorCount (pre++w) v := by
  induction pre with
  | nil => exact Nat.le_refl _
  | cons a pre ih =>
    simp only [List.cons_append, factorCount]
    split <;> omega

theorem factorCount_hit_le (v w : Word Letter) (hv : v ≠ []) :
    factorCount w v + 1 ≤ factorCount (v++w) v := by
  cases v with
  | nil => exact False.elim (hv rfl)
  | cons a v =>
    have hp : (a::v).IsPrefix (a::(v++w)) := by
      simpa only [List.cons_append] using List.prefix_append (a::v) w
    have hh := factorCount_prepend_le v w (a::v)
    simp only [List.cons_append, factorCount, if_pos hp]
    omega

theorem Packing.count_le_factorCount {w v : Word Letter} {c : Nat}
    (h : Packing v w c) (hv : v ≠ []) : c ≤ factorCount w v := by
  induction h with
  | zero => exact Nat.zero_le _
  | next pre rest ht ih =>
    have hh := factorCount_hit_le v rest hv
    have hp := factorCount_prepend_le pre (v++rest) v
    omega

theorem prefix_append_iff_of_length {α : Type} (v w z : Word α)
    (h : v.length ≤ w.length) : v.IsPrefix (w++z) ↔ v.IsPrefix w := by
  rw [List.prefix_iff_eq_take, List.prefix_iff_eq_take]
  rw [List.take_append_of_le_length h]

/-- At most `length(v)-1` new overlapping occurrences cross a concatenation
boundary. The stronger minimum handles short left components. -/
theorem factorCount_append_le_min (w z v : Word Letter) (hv : v ≠ []) :
    factorCount (w++z) v ≤ factorCount w v + factorCount z v + min w.length (v.length-1) := by
  induction w with
  | nil => simp [factorCount, hv]
  | cons a w ih =>
    have hvpos := List.length_pos_iff.mpr hv
    by_cases hl : v.length ≤ (a::w).length
    · have he := prefix_append_iff_of_length v (a::w) z hl
      have hmin : min (a::w).length (v.length-1) = v.length-1 := by omega
      have hmin' : min w.length (v.length-1) ≤ v.length-1 := Nat.min_le_right _ _
      simp only [List.cons_append, factorCount, hmin]
      by_cases hp : v.IsPrefix (a::w)
      · have hp' := he.mpr hp
        simp only [List.cons_append] at hp'
        simp only [if_pos hp, if_pos hp']
        omega
      · have hp' : ¬ v.IsPrefix (a::(w++z)) := by simpa only [List.cons_append] using
          (show ¬ v.IsPrefix ((a::w)++z) from fun hh => hp (he.mp hh))
        simp only [if_neg hp, if_neg hp', Nat.zero_add]
        omega
    · have hshort : (a::w).length < v.length := by omega
      have hz := factorCount_zero_of_short (a::w) v hshort
      have ht := factorCount_zero_of_short w v (by simp only [List.length_cons] at hshort; omega)
      have hmin : min (a::w).length (v.length-1) = (a::w).length := by omega
      have hmin' : min w.length (v.length-1) ≤ w.length := Nat.min_le_left _ _
      rw [hz, hmin]
      simp only [List.cons_append, factorCount, List.length_cons]
      split <;> omega

theorem factorCount_append_le (w z v : Word Letter) (hv : v ≠ []) :
    factorCount (w++z) v ≤ factorCount w v + factorCount z v + (v.length-1) := by
  have hh := factorCount_append_le_min w z v hv
  have hm := Nat.min_le_right w.length (v.length-1)
  omega

/-- Lift an internal block bound to a concatenation, charging one crossing
budget per block. The harmless last budget matches the manuscript's bound. -/
theorem factorCount_flatMap_le {α : Type} (w : Word α) (f : α → Word Letter)
    (v : Word Letter) (hv : v ≠ []) (m : Nat)
    (hf : ∀ a ∈ w, factorCount (f a) v ≤ m) :
    factorCount (w.flatMap f) v ≤ w.length*(m+v.length-1) := by
  induction w with
  | nil => simp [factorCount, hv]
  | cons a w ih =>
    have ha := hf a (by simp)
    have ht := ih (fun b hb => hf b (by simp [hb]))
    have hp := factorCount_append_le (f a) (w.flatMap f) v hv
    have hpos := List.length_pos_iff.mpr hv
    simp only [List.flatMap_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem muIterate_blocks (e : Nat) :
    muIterate (e+2) = (muIterate e).flatMap (fun a => muWord (mu a)) := by
  simp only [muIterate, muWord, List.flatMap_assoc]

theorem mu2_short_count (a : Letter) (v : Word Letter)
    (hv : v ≠ []) (hl : v.length ≤ 3) :
    factorCount (muWord (mu a)) v ≤
      (if v.length = 1 then 121 else if v.length = 2 then 61 else 41) := by
  cases v with
  | nil => exact False.elim (hv rfl)
  | cons b v =>
    cases v with
    | nil => exact mu2_count_one a b
    | cons c v =>
      cases v with
      | nil => exact mu2_count_two a b c
      | cons d v =>
        have he : v = [] := by simpa using hl
        subst v
        exact mu2_count_three a b c d

/-- The short-factor count used in Lemma 2, for every required iterate. -/
theorem muIterate_short_count (e : Nat) (v : Word Letter)
    (hv : v ≠ []) (hl : v.length ≤ 3) :
    factorCount (muIterate (e+2)) v ≤
      19^e * ((if v.length = 1 then 121 else if v.length = 2 then 61 else 41)+v.length-1) := by
  rw [muIterate_blocks]
  have hh := factorCount_flatMap_le (muIterate e) (fun a => muWord (mu a)) v hv
    (if v.length = 1 then 121 else if v.length = 2 then 61 else 41)
    (fun a _ => mu2_short_count a v hv hl)
  simpa only [muIterate_length] using hh

end GreedyLowerBound
