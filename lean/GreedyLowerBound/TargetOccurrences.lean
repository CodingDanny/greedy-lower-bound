import GreedyLowerBound.TargetPositions
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Prod

set_option autoImplicit false
namespace GreedyLowerBound

abbrev TargetOccurrence := Σ _ : Nat × Nat, Nat

def targetOccurrences (h : Nat) (D : List Bool) (L : Nat) : Finset TargetOccurrence :=
  ((Finset.range h).product (Finset.range h)).sigma (fun si =>
    Finset.range ((targetIndexWord h D si.1 si.2).length+1-L))

def targetOccurrenceFactor (h : Nat) (D : List Bool) (L : Nat) (o : TargetOccurrence) : List Nat :=
  slice (targetIndexWord h D o.1.1 o.1.2) o.2 L

theorem mem_targetOccurrences (h : Nat) (D : List Bool) (L : Nat) (o : TargetOccurrence) :
    o ∈ targetOccurrences h D L ↔
      o.1.1 < h ∧ o.1.2 < h ∧ o.2 < (targetIndexWord h D o.1.1 o.1.2).length+1-L := by
  simp [targetOccurrences, Finset.mem_sigma, Finset.mem_product, and_assoc]

theorem targetOccurrences_bound (h : Nat) (D : List Bool) (L : Nat) (o : TargetOccurrence)
    (ho : o ∈ targetOccurrences h D L) : o.2+L ≤ (targetIndexWord h D o.1.1 o.1.2).length := by
  have hh := ((mem_targetOccurrences h D L o).mp ho).2.2
  omega

theorem targetOccurrenceFactor_length (h : Nat) (D : List Bool) (L : Nat) (o : TargetOccurrence)
    (ho : o ∈ targetOccurrences h D L) : (targetOccurrenceFactor h D L o).length = L :=
  slice_length _ _ _ (targetOccurrences_bound h D L o ho)

theorem targetOccurrenceFactor_infix (h : Nat) (D : List Bool) (L : Nat) (o : TargetOccurrence) :
    (targetOccurrenceFactor h D L o).IsInfix (targetIndexWord h D o.1.1 o.1.2) := slice_infix _ _ _

/-- A fixed consecutive index factor occurs at most twice across all target
interiors. Equal parity forces equal global bit starts; that start fixes the
chunk, the target prefix, and then the unique position within its index word. -/
theorem targetOccurrence_fiber_card_le_two (h : Nat) (D : List Bool) (q L : Nat)
    (hh : 0 < h) (hD : D.length = h^2) (hU : UniqueWindows D q) (hL : 2*q+2 ≤ L)
    (v : List Nat) :
    ((targetOccurrences h D L).filter (fun o => targetOccurrenceFactor h D L o = v)).card ≤ 2 := by
  let fiber := (targetOccurrences h D L).filter (fun o => targetOccurrenceFactor h D L o = v)
  by_cases hn : fiber.Nonempty
  · obtain ⟨o₀, ho₀⟩ := hn
    obtain ⟨ho₀, he₀⟩ := Finset.mem_filter.mp ho₀
    have hlv : v.length = L := he₀ ▸ targetOccurrenceFactor_length h D L o₀ ho₀
    have hin₀ : v.IsInfix (targetIndexWord h D o₀.1.1 o₀.1.2) :=
      he₀ ▸ targetOccurrenceFactor_infix h D L o₀
    have hnodup : v.Nodup := (targetIndexWord_nodup h D o₀.1.1 o₀.1.2).sublist hin₀.sublist
    have hvn : v ≠ [] := by intro he; simp [he] at hlv; omega
    obtain ⟨lo, hlo, top, htop, hlt, hspan⟩ := nodup_index_span v hvn hnodup
    have hm₀ := (mem_targetOccurrences h D L o₀).mp ho₀
    have htoph := oneIndices_mem_lt (targetWindow h D o₀.1.1 o₀.1.2) top (hin₀.subset htop)
    rw [targetWindow_length h D o₀.1.1 o₀.1.2 hD hm₀.1 hm₀.2.1] at htoph
    have hin : ∀ o ∈ fiber, v.IsInfix (targetIndexWord h D o.1.1 o.1.2) := by
      intro o ho
      have he := (Finset.mem_filter.mp ho).2
      exact he ▸ targetOccurrenceFactor_infix h D L o
    have hb : ∀ o ∈ fiber,
        targetBitStart h o.1.1 o.1.2 top + (top+1-lo) ≤ (binaryEncode D).length := by
      intro o ho
      have hm := (mem_targetOccurrences h D L o).mp (Finset.mem_filter.mp ho).1
      exact targetBitStart_span_bound h D o.1.1 o.1.2 lo top hD hm.1 hm.2.1 htoph hlt
    have hinj : Set.InjOn (fun o : TargetOccurrence => targetBitStart h o.1.1 o.1.2 top % 2)
        (↑fiber : Set TargetOccurrence) := by
      intro o ho o' ho' hpar
      have hm := (mem_targetOccurrences h D L o).mp (Finset.mem_filter.mp ho).1
      have hm' := (mem_targetOccurrences h D L o').mp (Finset.mem_filter.mp ho').1
      have he := target_factor_reconstruct h D o.1.1 o.1.2 o'.1.1 o'.1.2 hD hm.1 hm.2.1
        hm'.1 hm'.2.1 v (hin o ho) (hin o' ho') lo top hlo htop hlt
      have hstart := encoded_same_parity_start D q (top+1-lo) _ _ hU (by omega)
        (hb o ho) (hb o' ho') hpar he
      have hsi := targetBitStart_injective h o.1.1 o.1.2 o'.1.1 o'.1.2 top hh hm.2.1 hm'.2.1 htoph hstart
      rcases o with ⟨⟨s, i⟩, p⟩
      rcases o' with ⟨⟨s', i'⟩, p'⟩
      change s = s' ∧ i = i' at hsi
      obtain ⟨rfl, rfl⟩ := hsi
      have hfac : slice (targetIndexWord h D s i) p L = slice (targetIndexWord h D s i) p' L :=
        (Finset.mem_filter.mp ho).2.trans (Finset.mem_filter.mp ho').2.symm
      dsimp only at hm hm'
      have hp := nodup_slice_start_unique (targetIndexWord h D s i) (targetIndexWord_nodup h D s i)
        p p' L (by omega) (by have hb := hm.2.2; omega) (by have hb := hm'.2.2; omega) hfac
      subst p'
      rfl
    have hc : fiber.card ≤ (Finset.range 2).card :=
      Finset.card_le_card_of_injOn (fun o => targetBitStart h o.1.1 o.1.2 top % 2)
        (fun o _ => Finset.mem_range.mpr (Nat.mod_lt _ (by decide))) hinj
    simpa only [Finset.card_range] using hc
  · have he : fiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    change fiber.card ≤ 2
    rw [he, Finset.card_empty]
    decide

/-- Counting fibers converts the verified multiplicity bound into a bound
for distinct index factors. -/
theorem targetOccurrences_card_le_twice_distinct (h : Nat) (D : List Bool) (q L : Nat)
    (hh : 0 < h) (hD : D.length = h^2) (hU : UniqueWindows D q) (hL : 2*q+2 ≤ L) :
    (targetOccurrences h D L).card ≤
      2*((targetOccurrences h D L).image (targetOccurrenceFactor h D L)).card := by
  rw [Finset.card_eq_sum_card_image (targetOccurrenceFactor h D L) (targetOccurrences h D L)]
  calc
    _ ≤ ∑ _v ∈ (targetOccurrences h D L).image (targetOccurrenceFactor h D L), 2 := by
      apply Finset.sum_le_sum
      intro v _
      exact targetOccurrence_fiber_card_le_two h D q L hh hD hU hL v
    _ = _ := by simp [Nat.mul_comm]

end GreedyLowerBound
