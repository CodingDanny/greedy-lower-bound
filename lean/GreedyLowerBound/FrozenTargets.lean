import GreedyLowerBound.AllPhases
import GreedyLowerBound.Freezing
import GreedyLowerBound.FactorBound
import GreedyLowerBound.SemanticsExistence

set_option autoImplicit false
namespace GreedyLowerBound

theorem List.IsInfix.flatMap {α β : Type} {v w : List α}
    (h : v.IsInfix w) (f : α → List β) : (v.flatMap f).IsInfix (w.flatMap f) := by
  obtain ⟨pre, post, rfl⟩ := h
  exact ⟨pre.flatMap f, post.flatMap f, by simp [List.flatMap_append]⟩

def eraseSymbol (a : Nat) (w : Word Nat) : Word Nat :=
  w.flatMap (fun b => if b = a then [] else [b])

theorem eraseSymbol_append (a : Nat) (v w : Word Nat) :
    eraseSymbol a (v ++ w) = eraseSymbol a v ++ eraseSymbol a w := by
  simp only [eraseSymbol, List.flatMap_append]

theorem eraseSymbol_flatMap (a : Nat) (w : Word Nat) (f : Nat → Word Nat) :
    eraseSymbol a (w.flatMap f) = w.flatMap (fun b => eraseSymbol a (f b)) := by
  simp only [eraseSymbol, List.flatMap_assoc]

theorem eraseSymbol_of_absent (a : Nat) (w : Word Nat) (h : a ∉ w) :
    eraseSymbol a w = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have hb : b ≠ a := by intro he; subst b; exact h (by simp)
    have hw : a ∉ w := fun hm => h (by simp [hm])
    simp only [eraseSymbol, List.flatMap_cons, if_neg hb, List.singleton_append]
    exact congrArg (List.cons b) (ih hw)

theorem eraseSymbol_replicate (a k : Nat) : eraseSymbol a (List.replicate k a) = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [eraseSymbol, List.replicate_succ] using ih

theorem erase_targetState (n : Nat) (A : Nat → Nat) (hA : Function.Injective A) (t : Nat) :
    eraseSymbol (A t) (targetState n A t) = lowerDigits n A t := by
  rw [targetState, eraseSymbol_append, eraseSymbol_replicate, List.nil_append]
  exact eraseSymbol_of_absent _ _ (lowerDigits_avoids_active n A t hA)

theorem Fragmentation.fragment_in_start {G : Grammar} (P : Fragmentation G)
    (w : Word Nat) (hw : w ∈ P.first :: P.rest.map Prod.snd) :
    w.IsInfix (G.rhs G.start) := by
  rw [P.start_eq]
  rcases List.mem_cons.mp hw with hw | hw
  · subst w
    exact (List.prefix_append _ _).isInfix
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    obtain ⟨left, right, he⟩ := List.append_of_mem hp
    refine ⟨P.first ++ left.flatMap (fun p => p.1 :: p.2) ++ [p.1],
      right.flatMap (fun p => p.1 :: p.2), ?_⟩
    simp [joinFragments, he, List.flatMap_append, List.append_assoc]

namespace PhaseStorage
variable {G H : Grammar} {h t : Nat} {D : List Bool}

def primaryDefinitions (S : PhaseStorage G h D t) : Finset Nat :=
  (Finset.range t).image (fun i => S.primary (i+1))

theorem primaryDefinitions_subset (S : PhaseStorage G h D t) :
    S.primaryDefinitions ⊆ G.defined := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  exact S.primary_defined (i+1) (by omega) (by have := Finset.mem_range.mp hi; omega)

theorem start_not_primaryDefinitions (S : PhaseStorage G h D t) :
    G.start ∉ S.primaryDefinitions := by
  intro hs
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hs
  exact S.primary_not_start (i+1) (by have := Finset.mem_range.mp hi; omega) he

theorem target_in_start (S : PhaseStorage G h D t) (n : Nat)
    (hn : n ∈ targetNumbers h D) : (targetState n S.primary t).IsInfix (G.rhs G.start) := by
  apply S.partition.fragment_in_start
  have hm : n = (targetNumbers h D).headD 0 ∨ n ∈ (targetNumbers h D).tail := by
    generalize targetNumbers h D = ns at *
    cases ns with
    | nil => simp at hn
    | cons a ns => simpa using hn
  rcases hm with rfl | hm
  · rw [← S.target_first]
    exact List.mem_cons_self
  · have hh : targetState n S.primary t ∈ (S.partition.rest.map Prod.snd).take
        ((targetNumbers h D).length-1) := by
      rw [S.target_rest]
      exact List.mem_map.mpr ⟨n, hm, rfl⟩
    exact List.mem_cons_of_mem _ (List.mem_of_mem_take hh)

theorem frozen_primary_value (S : PhaseStorage G h D t) (hh : 1 ≤ h)
    (hD : D.length = h^2) (value : Nat → Word Nat)
    (hv : (G.freeze S.primaryDefinitions).Semantics value) (i : Nat) (hi : i ≤ t) :
    value (S.primary i) = [S.primary i] := by
  apply hv.2
  intro hm
  have hm' := Finset.mem_sdiff.mp hm
  by_cases hi0 : i = 0
  · have hz := Grammar.generated_symbol_terminal S.wellFormed S.generates 0
      (inputWord_contains_zero h D hh hD)
    apply hz
    simpa [hi0, S.primary_zero] using hm'.1
  · apply hm'.2
    exact Finset.mem_image.mpr ⟨i-1, Finset.mem_range.mpr (by omega), by
      have he : i-1+1 = i := by omega
      rw [he]⟩

theorem frozen_targets_exist (S : PhaseStorage G h D t) (hh : 1 ≤ h)
    (hD : D.length = h^2) :
    ∃ w, (G.freeze S.primaryDefinitions).Generates w ∧
      ∀ n ∈ targetNumbers h D, (targetState n S.primary t).IsInfix w := by
  have hF := Grammar.freeze_wellFormed S.wellFormed S.start_not_primaryDefinitions
  obtain ⟨value, hv⟩ := (G.freeze S.primaryDefinitions).semantics_exists hF
  refine ⟨value G.start, ⟨value, hv, rfl⟩, ?_⟩
  intro n hn
  have hin := (S.target_in_start n hn).flatMap value
  have he : (targetState n S.primary t).flatMap value = targetState n S.primary t := by
    calc
      _ = (targetState n S.primary t).flatMap (fun a => [a]) := by
        apply List.flatMap_congr
        intro a ha
        obtain ⟨i, hi, rfl⟩ := targetState_mem n S.primary t a ha
        exact S.frozen_primary_value hh hD value hv i hi
      _ = _ := List.flatMap_singleton' _
  rw [he] at hin
  have hs := hv.1 G.start hF.1
  exact hs ▸ hin

/-- The erased frozen start word contains every hard target. Its factor
capacity is bounded by the actual final grammar size, even if erasure creates
empty interpretations. No assumption is made about the subsequent rounds. -/
theorem final_factor_capacity (S : PhaseStorage G h D h) (hh : 1 ≤ h)
    (hD : D.length = h^2) {steps : Nat} (run : GreedyRun G H steps) :
    ∃ w, (∀ n ∈ targetNumbers h D, (lowerDigits n S.primary h).IsInfix w) ∧
      ∀ L, 2 ≤ L → (distinctFactors w L).card ≤ H.size*(L-1) := by
  obtain ⟨w, hw, htargets⟩ := S.frozen_targets_exist hh hD
  have hs : H.start ∉ S.primaryDefinitions := by rw [run.start_eq]; exact S.start_not_primaryDefinitions
  obtain ⟨hWF, hgen, hsize⟩ := run.frozen_final_grammar S.wellFormed S.primaryDefinitions
    S.primaryDefinitions_subset hs w hw
  obtain ⟨value, hv, he⟩ := hgen
  refine ⟨eraseSymbol (S.primary h) w, ?_, ?_⟩
  · intro n hn
    have hin := (htargets n hn).flatMap (fun b => if b = S.primary h then [] else [b])
    change (eraseSymbol (S.primary h) (targetState n S.primary h)).IsInfix _ at hin
    rw [erase_targetState n S.primary S.primary_injective h] at hin
    exact hin
  · intro L hL
    let ev := fun i => eraseSymbol (S.primary h) (value i)
    have hrules : ∀ i ∈ (H.freeze S.primaryDefinitions).defined,
        ev i = ((H.freeze S.primaryDefinitions).rhs i).flatMap ev := by
      intro i hi
      change eraseSymbol (S.primary h) (value i) = _
      rw [hv.1 i hi, eraseSymbol_flatMap]
    have hterm : ∀ i ∉ (H.freeze S.primaryDefinitions).defined, (ev i).length ≤ 1 := by
      intro i hi
      simp only [ev, hv.2 i hi, eraseSymbol, List.flatMap_singleton]
      split_ifs <;> simp
    have hb := (H.freeze S.primaryDefinitions).interpreted_distinctFactors_card_le hWF ev hrules hterm L hL
    change (distinctFactors (eraseSymbol (S.primary h) (value H.start)) L).card ≤ _ at hb
    change value H.start = w at he
    rw [he] at hb
    exact hb.trans (Nat.mul_le_mul_right (L-1) hsize)

end PhaseStorage

/-- Complete algorithmic reduction: the final grammar from any terminal run
has enough factor capacity for all erased target blocks. Only the separate
finite-word counting argument remains to turn this into a numeric bound. -/
theorem input_factor_capacity (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) (H : Grammar) (steps : Nat)
    (run : GreedyRun (inputGrammar h D) H steps) (hterm : H.Terminal) :
    ∃ A : Nat → Nat, Function.Injective A ∧ ∃ w,
      (∀ n ∈ targetNumbers h D, (lowerDigits n A h).IsInfix w) ∧
      ∀ L, 2 ≤ L → (distinctFactors w L).card ≤ H.size*(L-1) := by
  obtain ⟨K, m, k, S, _, _, hrest, _, _⟩ := input_all_phases h D hh hD H steps run hterm
  obtain ⟨w, ht, hc⟩ := S.final_factor_capacity hh hD hrest
  exact ⟨S.primary, S.primary_injective, w, ht, hc⟩

end GreedyLowerBound
