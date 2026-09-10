import GreedyLowerBound.MaximumOccurrences
import GreedyLowerBound.MorphismPowerFree
import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace GreedyLowerBound

universe u v
variable {α : Type u} {β : Type v}

/-- Homomorphic projection of a packing preserves its count. To interpret the
result as occurrences of a nonempty factor, require its projected factor to
be nonempty at the use site. -/
theorem Packing.flatMap {w s : Word α} {c : Nat} (h : Packing w s c)
    (f : α → Word β) : Packing (w.flatMap f) (s.flatMap f) c := by
  induction h with
  | zero s => exact Packing.zero _
  | next pre rest ht ih =>
    simpa only [List.flatMap_append] using
      Packing.next (pre.flatMap f) (rest.flatMap f) ih

/-- `none` is the padding symbol X; `some a` is a marker. -/
def auxiliaryWord (L : Nat) (w : Word α) : Word (Option α) :=
  w.flatMap fun a => List.replicate L none ++ [some a]

def markers (w : Word (Option α)) : Word α := w.flatMap Option.toList

theorem markers_append (w z : Word (Option α)) :
    markers (w++z) = markers w ++ markers z := List.flatMap_append

theorem markers_padding (L : Nat) : markers (List.replicate L (none : Option α)) = [] := by
  induction L with
  | zero => rfl
  | succ L ih => simpa only [List.replicate_succ, markers, List.flatMap_cons,
      Option.toList_none, List.nil_append] using ih

theorem markers_auxiliaryWord (L : Nat) (w : Word α) : markers (auxiliaryWord L w) = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [auxiliaryWord, List.flatMap_cons, markers_append, markers_padding]
    simpa only [markers, List.flatMap_cons, List.flatMap_nil, Option.toList_some,
      List.append_nil, List.nil_append, List.singleton_append] using congrArg (List.cons a) ih

theorem auxiliaryWord_length (L : Nat) (w : Word α) :
    (auxiliaryWord L w).length = w.length*(L+1) := by
  induction w with
  | nil => simp [auxiliaryWord]
  | cons a w ih =>
    simp only [auxiliaryWord, List.flatMap_cons, List.length_append, List.length_replicate,
      List.length_singleton, List.length_cons, List.length_nil] at *
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Prefixes end at an offset between zero and L in the next padded block. -/
theorem auxiliaryWord_prefix_bounds (L : Nat) (w : Word α) (n : Nat) :
    (markers ((auxiliaryWord L w).take n)).length*(L+1) ≤
        ((auxiliaryWord L w).take n).length ∧
    ((auxiliaryWord L w).take n).length ≤
        (markers ((auxiliaryWord L w).take n)).length*(L+1)+L := by
  induction w generalizing n with
  | nil => simp [auxiliaryWord, markers]
  | cons a w ih =>
    have hblock : (List.replicate L (none : Option α) ++ [some a]).length = L+1 := by simp
    by_cases hn : n ≤ L
    · have ht : (auxiliaryWord L (a::w)).take n = List.replicate n none := by
        simp only [auxiliaryWord, List.flatMap_cons]
        rw [List.append_assoc, List.take_append_of_le_length (by simpa using hn)]
        simp [List.take_replicate, Nat.min_eq_left hn]
      rw [ht, markers_padding]
      simp only [List.length_nil, Nat.zero_mul, List.length_replicate, Nat.zero_add]
      exact ⟨Nat.zero_le _, hn⟩
    · have ht : (auxiliaryWord L (a::w)).take n =
          (List.replicate L none ++ [some a]) ++ (auxiliaryWord L w).take (n-(L+1)) := by
        simp only [auxiliaryWord, List.flatMap_cons]
        rw [List.take_append_eq_append_take, List.take_of_length_le (by rw [hblock]; omega), hblock]
      rw [ht, markers_append, markers_append, markers_padding]
      have hh := ih (n-(L+1))
      simp only [markers, List.flatMap_cons, List.flatMap_nil, Option.toList_some,
        List.append_nil, List.nil_append, List.singleton_append, List.length_cons,
        List.length_append, hblock, Nat.add_mul, Nat.one_mul] at *
      omega

theorem auxiliaryWord_prefix_bounds_of_prefix (L : Nat) (w : Word α)
    (p : Word (Option α)) (hp : p.IsPrefix (auxiliaryWord L w)) :
    (markers p).length*(L+1) ≤ p.length ∧
      p.length ≤ (markers p).length*(L+1)+L := by
  have he := List.prefix_iff_eq_take.mp hp
  simpa only [← he] using auxiliaryWord_prefix_bounds L w p.length

/-- Equation (8), proved from prefix bounds at both ends of the occurrence. -/
theorem auxiliary_factor_length (L : Nat) (w : Word α) (pre v rest : Word (Option α))
    (he : auxiliaryWord L w = pre++(v++rest)) :
    v.length ≤ (markers v).length*(L+1)+L := by
  have hp : pre.IsPrefix (auxiliaryWord L w) := by rw [he]; exact List.prefix_append _ _
  have hv : (pre++v).IsPrefix (auxiliaryWord L w) := by
    rw [he, ← List.append_assoc]
    exact List.prefix_append _ _
  have hlo := (auxiliaryWord_prefix_bounds_of_prefix L w pre hp).1
  have hup := (auxiliaryWord_prefix_bounds_of_prefix L w (pre++v) hv).2
  rw [markers_append, List.length_append, List.length_append, Nat.add_mul] at hup
  omega

theorem auxiliary_factor_length_lt (L : Nat) (w : Word α) (pre v rest : Word (Option α))
    (he : auxiliaryWord L w = pre++(v++rest)) :
    v.length < ((markers v).length+1)*(L+1) := by
  have hh := auxiliary_factor_length L w pre v rest he
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem Packing.auxiliary_markers (L : Nat) (w : Word α) (v : Word (Option α)) (c : Nat)
    (h : Packing v (auxiliaryWord L w) c) : Packing (markers v) w c := by
  have hh := h.flatMap Option.toList
  change Packing (markers v) (markers (auxiliaryWord L w)) c at hh
  simpa only [markers_auxiliaryWord] using hh

theorem Packing.auxiliary_length_bound (L : Nat) (w : Word α) (v : Word (Option α))
    (c : Nat) (h : Packing v (auxiliaryWord L w) c) (hc : 0 < c) :
    v.length < ((markers v).length+1)*(L+1) := by
  have hex : ∀ s : Word (Option α), Packing v s c →
      ∃ pre rest, s = pre++(v++rest) := by
    intro s hs
    cases hs with
    | zero => omega
    | next pre rest ht => exact ⟨pre, rest, rfl⟩
  obtain ⟨pre, rest, he⟩ := hex _ h
  exact auxiliary_factor_length_lt L w pre v rest he

end GreedyLowerBound
