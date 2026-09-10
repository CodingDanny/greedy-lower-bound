import GreedyLowerBound.Greedy
import GreedyLowerBound.AuxiliaryRenaming

set_option autoImplicit false

namespace GreedyLowerBound

theorem Packing.symbol_count_bound {α : Type} [DecidableEq α]
    {v w : Word α} {c : Nat} (h : Packing v w c) (a : α) :
    c * v.count a ≤ w.count a := by
  induction h with
  | zero => simp
  | next pre rest ht ih =>
    simp only [List.count_append, Nat.add_mul, Nat.one_mul]
    omega

theorem Scan.preserves_absent_factor_symbol {α : Type} [DecidableEq α]
    {v s t : Word α} {fresh : α} {c : Nat} (h : Scan v fresh s t c)
    (a : α) (ha : a ∉ v) (hf : fresh ≠ a) : t.count a = s.count a := by
  induction h with
  | nil => rfl
  | hit h ih =>
    simp only [List.count_cons_of_ne hf, List.count_append, List.count_eq_zero.mpr ha,
      Nat.zero_add, ih]
  | skip hn h ih => simp only [List.count_cons, ih]

namespace Grammar

def symbolCount (G : Grammar) (a : Nat) : Nat := ∑ i ∈ G.defined, (G.rhs i).count a

theorem frequency_le_symbolCount (G : Grammar) (v : Word Nat) (a : Nat)
    (hv : v ≠ []) (ha : a ∈ v) : G.frequency v ≤ G.symbolCount a := by
  apply Finset.sum_le_sum
  intro i hi
  have hp := (scanCount_is_maximum v (G.rhs i) hv).1
  have hh := hp.symbol_count_bound a
  have hc : 1 ≤ v.count a := List.count_pos_iff.mpr ha
  have hm := Nat.mul_le_mul_left (scanCount v (G.rhs i)) hc
  simp only [Nat.mul_one] at hm
  omega

theorem eligible_excludes_single_symbol (G : Grammar) (v : Word Nat) (a : Nat)
    (hv : G.Eligible v) (ha : G.symbolCount a ≤ 1) : a ∉ v := by
  intro ham
  have hvn : v ≠ [] := by intro he; have hh := hv.1; simp only [he, List.length_nil] at hh; omega
  have hf := G.frequency_le_symbolCount v a hvn ham
  have hc := hv.2
  omega

/-- A literal terminal separator occurs once in the start right-hand side
and nowhere in any other defined right-hand side. -/
def StartSeparator (G : Grammar) (z : Nat) : Prop :=
  G.start ∈ G.defined ∧ z ∉ G.defined ∧
    ∀ i ∈ G.defined, (G.rhs i).count z = if i = G.start then 1 else 0

theorem StartSeparator.symbolCount {G : Grammar} {z : Nat} (h : G.StartSeparator z) :
    G.symbolCount z = 1 := by
  unfold Grammar.symbolCount
  calc
    _ = ∑ i ∈ G.defined, (if i = G.start then 1 else 0 : Nat) :=
      Finset.sum_congr rfl h.2.2
    _ = 1 := by simp [h.1]

theorem StartSeparator.mem_start {G : Grammar} {z : Nat} (h : G.StartSeparator z) :
    z ∈ G.rhs G.start := by
  have hh := h.2.2 G.start h.1
  apply List.count_pos_iff.mp
  simpa only [if_pos rfl] using (show 0 < (G.rhs G.start).count z by rw [hh]; simp)

end Grammar

/-- The literal separator invariant is preserved by every Greedy round. -/
theorem GlobalStep.preserves_separator {G H : Grammar} {v : Word Nat}
    {fresh z : Nat} {counts : Nat → Nat} (hr : GlobalStep G H v fresh counts)
    (hv : G.Eligible v) (hz : G.StartSeparator z) : H.StartSeparator z := by
  have hvz : z ∉ v := G.eligible_excludes_single_symbol v z hv (by rw [hz.symbolCount])
  have hfz : fresh ≠ z := by
    intro he
    have hh := hr.fresh_rhs G.start hz.1
    rw [he] at hh
    exact hh hz.mem_start
  refine ⟨?_, ?_, ?_⟩
  · rw [hr.start, hr.domain]
    exact Finset.mem_insert_of_mem hz.1
  · rw [hr.domain]
    simp only [Finset.mem_insert, not_or]
    exact ⟨Ne.symm hfz, hz.2.1⟩
  · intro i hi
    rw [hr.domain] at hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      rw [hr.new_rule, List.count_eq_zero.mpr hvz, hr.start, if_neg hr.fresh_start]
    · rw [(hr.scans i hi).preserves_absent_factor_symbol z hvz hfz, hr.start]
      exact hz.2.2 i hi

theorem GreedyStep.preserves_separator {G H : Grammar} {z : Nat}
    (h : GreedyStep G H) (hz : G.StartSeparator z) : H.StartSeparator z := by
  obtain ⟨v, fresh, hr, hv, _⟩ := h
  exact hr.preserves_separator hv hz

theorem GreedyRun.preserves_separator {G H : Grammar} {n z : Nat}
    (h : GreedyRun G H n) (hz : G.StartSeparator z) : H.StartSeparator z := by
  induction h with
  | nil => exact hz
  | cons hs ht ih => exact ih (hs.preserves_separator hz)

/-- No eligible factor at any later time can cross a protected separator. -/
theorem GreedyRun.eligible_avoids_separator {G H : Grammar} {n z : Nat}
    (h : GreedyRun G H n) (hz : G.StartSeparator z) (v : Word Nat) (hv : H.Eligible v) :
    z ∉ v := by
  have hh := h.preserves_separator hz
  exact H.eligible_excludes_single_symbol v z hv (by rw [hh.symbolCount])

end GreedyLowerBound
