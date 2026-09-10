import GreedyLowerBound.AuxiliaryBound
import Mathlib.Logic.Function.Basic

set_option autoImplicit false

namespace GreedyLowerBound

universe u v
variable {α : Type u} {β : Type v}

theorem Packing.map {w s : Word α} {c : Nat} (h : Packing w s c) (f : α → β) :
    Packing (w.map f) (s.map f) c := by
  simpa only [← List.map_eq_flatMap] using h.flatMap (fun a => [f a])

theorem Packing.factor_mem {w s : Word α} {c : Nat} (h : Packing w s c)
    (hc : 0 < c) (a : α) (ha : a ∈ w) : a ∈ s := by
  cases h with
  | zero => omega
  | next pre rest ht => exact List.mem_append_right _ (List.mem_append_left _ ha)

/-- Lemma 2 is invariant under any injective renaming of the padding symbol
and the three markers. This includes their actual natural-number names in the
grammar model; no restriction to the canonical Option alphabet remains. -/
theorem auxiliary_gain_bound_renamed (e L : Nat) (he : 2 ≤ e)
    (f : Option Letter → α) (hf : Function.Injective f)
    (w : Word α) (c : Nat)
    (h : Packing w ((auxiliaryWord L (muIterate e)).map f) c)
    (hc : 2 ≤ c) (hm : ∃ a ∈ w, a ≠ f none) :
    16*replacementGain c w.length ≤ (15*19^e*(L+1) : Nat) := by
  classical
  let g := Function.invFun f
  have hgf : ∀ a, g (f a) = a := Function.leftInverse_invFun hf
  have hp := h.map g
  have hback : ((auxiliaryWord L (muIterate e)).map f).map g = auxiliaryWord L (muIterate e) := by
    simp only [List.map_map]
    have heq : g ∘ f = id := funext hgf
    rw [heq, List.map_id]
  rw [hback] at hp
  have hm' : markers (w.map g) ≠ [] := by
    obtain ⟨a, ha, han⟩ := hm
    have hain := h.factor_mem (by omega) a ha
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hain
    have hbn : b ≠ none := by intro heq; subst b; exact han hb.symm
    cases b with
    | none => exact False.elim (hbn rfl)
    | some b =>
      have hga : g a = some b := by rw [← hb, hgf]
      have hmb : some b ∈ w.map g := by
        rw [← hga]
        exact List.mem_map.mpr ⟨a, ha, rfl⟩
      have hbmark : b ∈ markers (w.map g) := by
        exact List.mem_flatMap.mpr ⟨some b, hmb, by simp⟩
      intro hz
      rw [hz] at hbmark
      exact List.not_mem_nil hbmark
  have hh := auxiliary_gain_bound e L he (w.map g) c hp hc hm'
  simpa only [List.length_map] using hh

end GreedyLowerBound
