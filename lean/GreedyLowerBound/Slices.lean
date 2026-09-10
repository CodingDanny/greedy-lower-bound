import GreedyLowerBound.Words
import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace GreedyLowerBound

universe u
variable {α : Type u}

def slice (w : Word α) (p L : Nat) : Word α := (w.drop p).take L

theorem slice_get (w : Word α) (p L k : Nat) (hk : k < L) :
    (slice w p L)[k]? = w[p+k]? := by
  simp only [slice, List.getElem?_take_of_lt hk, List.getElem?_drop]

theorem slice_length (w : Word α) (p L : Nat) (hb : p+L ≤ w.length) :
    (slice w p L).length = L := by
  simp only [slice, List.length_take, List.length_drop]
  omega

theorem slice_append_left (w z : Word α) (p L : Nat) (hb : p+L ≤ w.length) :
    slice (w++z) p L = slice w p L := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < L
  · rw [slice_get _ _ _ _ hk, slice_get _ _ _ _ hk]
    exact List.getElem?_append_left (by omega)
  · simp only [slice, List.getElem?_take, hk, ↓reduceIte]

theorem slice_append_right (w z : Word α) (p L : Nat) (hb : w.length ≤ p) :
    slice (w++z) p L = slice z (p-w.length) L := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < L
  · rw [slice_get _ _ _ _ hk, slice_get _ _ _ _ hk,
      List.getElem?_append_right (by omega)]
    congr 1
    omega
  · simp only [slice, List.getElem?_take, hk, ↓reduceIte]

/-- Any factor in a concatenation is contained in one component or crosses
one of its internal boundaries. The crossed boundary is strictly inside the
factor. The statement also allows empty component words. -/
theorem slice_flatMap_cases {β : Type u} (rhs : Word α) (value : α → Word β)
    (p L : Nat) (hL : 0 < L) (hb : p+L ≤ (rhs.flatMap value).length) :
    (∃ j ∈ rhs, ∃ q, q+L ≤ (value j).length ∧
      slice (rhs.flatMap value) p L = slice (value j) q L) ∨
    (∃ i, i < rhs.length ∧ p < ((rhs.take i).flatMap value).length ∧
      ((rhs.take i).flatMap value).length < p+L) := by
  induction rhs generalizing p with
  | nil => simp only [List.flatMap_nil, List.length_nil] at hb; omega
  | cons a rhs ih =>
    simp only [List.flatMap_cons, List.length_append] at hb
    by_cases hp : (value a).length ≤ p
    · have hb' : p-(value a).length+L ≤ (rhs.flatMap value).length := by omega
      rcases ih (p-(value a).length) hb' with hin | hcross
      · obtain ⟨j, hj, q, hq, he⟩ := hin
        refine Or.inl ⟨j, List.mem_cons.mpr (Or.inr hj), q, hq, ?_⟩
        rw [List.flatMap_cons, slice_append_right _ _ _ _ hp]
        exact he
      · obtain ⟨i, hi, hleft, hright⟩ := hcross
        refine Or.inr ⟨i+1, ?_, ?_, ?_⟩
        · simpa using hi
        · simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
          omega
        · simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
          omega
    · by_cases hwhole : p+L ≤ (value a).length
      · refine Or.inl ⟨a, by simp, p, hwhole, ?_⟩
        simpa only [List.flatMap_cons] using
          (slice_append_left (value a) (rhs.flatMap value) p L hwhole)
      · refine Or.inr ⟨1, ?_, ?_, ?_⟩
        · have hnon : rhs ≠ [] := by intro he; simp only [he, List.flatMap_nil,
            List.length_nil, Nat.add_zero] at hb; omega
          have hh := List.length_pos_iff.mpr hnon
          simp only [List.length_cons]; omega
        · simpa using (show p < (value a).length by omega)
        · simpa using (show (value a).length < p+L by omega)

end GreedyLowerBound
