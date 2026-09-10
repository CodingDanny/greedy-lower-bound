import GreedyLowerBound.Substitution

set_option autoImplicit false

namespace GreedyLowerBound

universe u
variable {α : Type u} [DecidableEq α]

/-- Number of disjoint occurrences selected by the leftmost scan.
The empty factor is assigned zero and is excluded by Greedy eligibility. -/
def scanCount (v s : Word α) : Nat :=
  if _hv : v = [] then 0
  else if hp : v.IsPrefix s then
    scanCount v (s.drop v.length) + 1
  else match s with
    | [] => 0
    | _ :: tail => scanCount v tail
termination_by s.length
decreasing_by
  · have hl := hp.length_le
    have hvlen : 0 < v.length := List.length_pos_iff.mpr _hv
    simp only [List.length_drop]
    omega
  · simp

theorem Scan.count_eq {v s t : Word α} {fresh : α} {c : Nat}
    (h : Scan v fresh s t c) (hv : v ≠ []) : c = scanCount v s := by
  induction h with
  | nil => simp [scanCount, hv]
  | hit h ih =>
    rw [scanCount]
    simp only [hv, ↓reduceDIte, List.prefix_append, List.drop_left, ih]
  | skip hn h ih =>
    rw [scanCount]
    simp only [hv, hn, ↓reduceDIte, ih]

theorem Scan.exists_output (v s : Word α) (fresh : α) (hv : v ≠ []) :
    ∃ t, Scan v fresh s t (scanCount v s) := by
  generalize hn : s.length = n
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    by_cases hp : v.IsPrefix s
    · have hl := hp.length_le
      have hvlen := List.length_pos_iff.mpr hv
      have hlen : (s.drop v.length).length < n := by
        simp only [List.length_drop]
        omega
      obtain ⟨t, ht⟩ := ih _ hlen (s.drop v.length) rfl
      refine ⟨fresh :: t, ?_⟩
      have hs := List.prefix_iff_eq_append.mp hp
      have hhit := Scan.hit ht
      rw [hs] at hhit
      rw [scanCount]
      simpa only [hv, hp, ↓reduceDIte] using hhit
    · cases s with
      | nil => exact ⟨[], by simpa [scanCount, hv] using (Scan.nil (v := v) (fresh := fresh))⟩
      | cons a s =>
        have hlen : s.length < n := by simp only [List.length_cons] at hn; omega
        obtain ⟨t, ht⟩ := ih _ hlen s rfl
        refine ⟨a :: t, ?_⟩
        rw [scanCount]
        simpa only [hv, hp, ↓reduceDIte] using Scan.skip hp ht

theorem Scan.count_unique {v s t t' : Word α} {fresh fresh' : α} {c c' : Nat}
    (h : Scan v fresh s t c) (h' : Scan v fresh' s t' c') (hv : v ≠ []) : c = c' :=
  (h.count_eq hv).trans (h'.count_eq hv).symm

end GreedyLowerBound
