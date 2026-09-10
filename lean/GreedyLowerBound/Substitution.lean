import GreedyLowerBound.Words

set_option autoImplicit false

namespace GreedyLowerBound

universe u v
variable {α : Type u} {β : Type v}

/-- One complete left-to-right scan. A hit consumes the entire factor.
A skip is permitted only when the factor is not a prefix at that position.
The last index counts replacements. The factor is required to be nonempty
by the algorithm that uses this relation. -/
inductive Scan (v : Word α) (fresh : α) : Word α → Word α → Nat → Prop
  | nil : Scan v fresh [] [] 0
  | hit {s t : Word α} {c : Nat} :
      Scan v fresh s t c → Scan v fresh (v ++ s) (fresh :: t) (c + 1)
  | skip {a : α} {s t : Word α} {c : Nat} :
      ¬ v.IsPrefix (a :: s) →
      Scan v fresh s t c → Scan v fresh (a :: s) (a :: t) c

namespace Scan

variable {v s t : Word α} {fresh : α} {c : Nat}

/-- Exact old-versus-new length identity, without truncated subtraction. -/
theorem length_accounting (h : Scan v fresh s t c) :
    s.length + c = t.length + c * v.length := by
  induction h with
  | nil => simp
  | @hit s t c h ih =>
      simp only [List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  | @skip a s t c hn h ih =>
      simp only [List.length_cons]
      omega

/-- A substitution preserves every interpretation satisfying the new equation.
This also applies to interpretations that freeze selected nonterminals. -/
theorem preserves_interpretation (h : Scan v fresh s t c)
    (interpret : α → Word β) (hf : interpret fresh = v.flatMap interpret) :
    t.flatMap interpret = s.flatMap interpret := by
  induction h with
  | nil => rfl
  | hit h ih =>
      simp only [List.flatMap_cons, List.flatMap_append, hf, ih]
  | skip hn h ih =>
      simp only [List.flatMap_cons, ih]

/-- The size saved in a scanned right-hand side is the occurrence benefit. -/
theorem benefit (h : Scan v fresh s t c) (hv : 1 ≤ v.length) :
    t.length + c * (v.length - 1) = s.length := by
  have ha := h.length_accounting
  have he : v.length - 1 + 1 = v.length := by omega
  have hm : c * v.length = c * (v.length - 1) + c := by
    calc
      c * v.length = c * (v.length - 1 + 1) := congrArg (fun k => c * k) he.symm
      _ = c * (v.length - 1) + c := by rw [Nat.mul_add, Nat.mul_one]
  omega

theorem output_mem (h : Scan v fresh s t c) (x : α) (hx : x ∈ t) :
    x = fresh ∨ x ∈ s := by
  induction h with
  | nil => simp at hx
  | hit h ih =>
    rcases List.mem_cons.mp hx with he | hm
    · exact Or.inl he
    · rcases ih hm with he | hm
      · exact Or.inl he
      · exact Or.inr (List.mem_append_right _ hm)
  | skip hn h ih =>
    rcases List.mem_cons.mp hx with he | hm
    · exact Or.inr (List.mem_cons.mpr (Or.inl he))
    · rcases ih hm with he | hm
      · exact Or.inl he
      · exact Or.inr (List.mem_cons.mpr (Or.inr hm))

theorem zero_eq (h : Scan v fresh s t c) (hc : c = 0) : s = t := by
  induction h with
  | nil => rfl
  | hit h ih => omega
  | skip hn h ih => exact congrArg (List.cons _) (ih hc)

theorem nonempty_output (h : Scan v fresh s t c) (hs : s ≠ []) : t ≠ [] := by
  cases h with
  | nil => exact False.elim (hs rfl)
  | hit h => simp
  | skip hn h => simp

theorem factor_mem_of_positive (h : Scan v fresh s t c) (hc : 0 < c)
    (x : α) (hx : x ∈ v) : x ∈ s := by
  induction h with
  | nil => omega
  | hit h ih => exact List.mem_append_left _ hx
  | skip hn h ih => exact List.mem_cons.mpr (Or.inr (ih hc))

theorem factor_length_le (h : Scan v fresh s t c) (hc : 0 < c) :
    v.length ≤ s.length := by
  induction h with
  | nil => omega
  | hit h ih => simp only [List.length_append]; omega
  | skip hn h ih => have hh := ih hc; simp only [List.length_cons]; omega

end Scan

end GreedyLowerBound
