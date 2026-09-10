import GreedyLowerBound.Substitution
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

namespace GreedyLowerBound

/-- Symbols have natural-number names. Exactly the names in `defined` are
nonterminals; all other names are terminals. This allows a frozen primary
to become a terminal by removing its definition, without renaming symbols. -/
structure Grammar where
  defined : Finset Nat
  rhs : Nat → Word Nat
  start : Nat

variable {G H : Grammar} {F : Finset Nat}

namespace Grammar

def size (G : Grammar) : Nat := ∑ i ∈ G.defined, (G.rhs i).length

/-- A finite nonempty grammar with nonempty right-hand sides and an acyclic
dependency graph, certified by a natural-number rank. Names need not be in
topological or creation order. -/
def WellFormed (G : Grammar) : Prop :=
  G.start ∈ G.defined ∧
  (∀ i ∈ G.defined, G.rhs i ≠ []) ∧
  ∃ rank : Nat → Nat, ∀ i ∈ G.defined, ∀ j ∈ G.defined,
    j ∈ G.rhs i → rank j < rank i

/-- Equations determining the terminal expansion of each symbol. -/
def Semantics (G : Grammar) (value : Nat → Word Nat) : Prop :=
  (∀ i ∈ G.defined, value i = (G.rhs i).flatMap value) ∧
  (∀ i ∉ G.defined, value i = [i])

def Generates (G : Grammar) (w : Word Nat) : Prop :=
  ∃ value, G.Semantics value ∧ value G.start = w

/-- Removing definitions makes precisely those symbol names terminal. -/
def freeze (G : Grammar) (F : Finset Nat) : Grammar :=
  { G with defined := G.defined \ F }

theorem freeze_size_le (G : Grammar) (F : Finset Nat) :
    (G.freeze F).size ≤ G.size := by
  apply Finset.sum_le_sum_of_subset
  exact Finset.sdiff_subset

theorem freeze_wellFormed (hG : G.WellFormed) (hs : G.start ∉ F) :
    (G.freeze F).WellFormed := by
  rcases hG with ⟨hstart, hne, rank, hrank⟩
  refine ⟨?_, ?_, rank, ?_⟩
  · exact Finset.mem_sdiff.mpr ⟨hstart, hs⟩
  · intro i hi
    exact hne i (Finset.mem_sdiff.mp hi).1
  · intro i hi j hj hm
    exact hrank i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).1 hm

end Grammar

/-- Exact simultaneous global replacement in all old right-hand sides,
followed by addition of the fresh definition. The count function records
the left-to-right scans; no scan of the newly added rule is included. -/
structure GlobalStep (G H : Grammar) (v : Word Nat) (fresh : Nat)
    (counts : Nat → Nat) : Prop where
  fresh_defined : fresh ∉ G.defined
  fresh_start : fresh ≠ G.start
  fresh_rhs : ∀ i ∈ G.defined, fresh ∉ G.rhs i
  fresh_factor : fresh ∉ v
  domain : H.defined = insert fresh G.defined
  start : H.start = G.start
  new_rule : H.rhs fresh = v
  scans : ∀ i ∈ G.defined, Scan v fresh (G.rhs i) (H.rhs i) (counts i)

/-- Interpret the new symbol by the old interpretation of its definition. -/
def extendInterpretation (value : Nat → Word Nat) (v : Word Nat) (fresh : Nat) :
    Nat → Word Nat := fun i => if i = fresh then v.flatMap value else value i

theorem flatMap_extendInterpretation (value : Nat → Word Nat) (v w : Word Nat)
    (fresh : Nat) (h : fresh ∉ w) :
    w.flatMap (extendInterpretation value v fresh) = w.flatMap value := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      have ha : a ≠ fresh := by intro he; subst a; exact h (by simp)
      have hw : fresh ∉ w := by intro hm; exact h (by simp [hm])
      simp only [List.flatMap_cons, extendInterpretation, if_neg ha]
      rw [ih hw]

namespace GlobalStep

variable {v : Word Nat} {fresh : Nat} {counts : Nat → Nat}

/-- The exact global size identity, including the newly created rule. -/
theorem size_accounting (h : GlobalStep G H v fresh counts) (hv : 1 ≤ v.length) :
    H.size + (∑ i ∈ G.defined, counts i) * (v.length - 1) = G.size + v.length := by
  have hs : (∑ i ∈ G.defined, (H.rhs i).length) +
      (∑ i ∈ G.defined, counts i) * (v.length - 1) = G.size := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i hi => (h.scans i hi).benefit hv)
  have hh : H.size = v.length + ∑ i ∈ G.defined, (H.rhs i).length := by
    simp only [Grammar.size, h.domain, Finset.sum_insert h.fresh_defined, h.new_rule]
  omega

/-- Removing a fixed set of old definitions commutes with the semantic effect
of every later global substitution, even when that substitution also edits a
removed right-hand side. -/
theorem preserves_frozen_semantics (h : GlobalStep G H v fresh counts)
    (hf : fresh ∉ F) (value : Nat → Word Nat) (hv : (G.freeze F).Semantics value) :
    (H.freeze F).Semantics (extendInterpretation value v fresh) := by
  let next := extendInterpretation value v fresh
  have hn : next fresh = v.flatMap next := by
    rw [flatMap_extendInterpretation value v v fresh h.fresh_factor]
    simp [next, extendInterpretation]
  constructor
  · intro i hi
    have hi' := Finset.mem_sdiff.mp hi
    have him : i ∈ insert fresh G.defined := by simpa [Grammar.freeze, h.domain] using hi'.1
    rcases Finset.mem_insert.mp him with he | him
    · subst i
      simpa only [Grammar.freeze, h.new_rule] using hn
    · by_cases he : i = fresh
      · subst i; exact False.elim (h.fresh_defined him)
      have hvold := hv.1 i (Finset.mem_sdiff.mpr ⟨him, hi'.2⟩)
      have hscan := (h.scans i him).preserves_interpretation next hn
      have hmap := flatMap_extendInterpretation value v (G.rhs i) fresh (h.fresh_rhs i him)
      change next i = (H.rhs i).flatMap next
      rw [hscan, hmap]
      simpa only [next, extendInterpretation, if_neg he] using hvold
  · intro i hi
    have he : i ≠ fresh := by
      intro he; subst i
      apply hi
      exact Finset.mem_sdiff.mpr ⟨by simp [Grammar.freeze, h.domain], hf⟩
    have hold : i ∉ (G.freeze F).defined := by
      intro hm
      apply hi
      rcases Finset.mem_sdiff.mp hm with ⟨hm, hnF⟩
      exact Finset.mem_sdiff.mpr ⟨by simpa [Grammar.freeze, h.domain] using
        (Finset.mem_insert_of_mem hm : i ∈ insert fresh G.defined), hnF⟩
    simpa only [extendInterpretation, if_neg he] using hv.2 i hold

theorem preserves_frozen_word (h : GlobalStep G H v fresh counts)
    (hf : fresh ∉ F) (w : Word Nat) (hw : (G.freeze F).Generates w) :
    (H.freeze F).Generates w := by
  rcases hw with ⟨value, hv, hw⟩
  refine ⟨extendInterpretation value v fresh, h.preserves_frozen_semantics hf value hv, ?_⟩
  simpa only [Grammar.freeze, h.start, extendInterpretation,
    if_neg (Ne.symm h.fresh_start)] using hw

theorem preserves_word (h : GlobalStep G H v fresh counts)
    (w : Word Nat) (hw : G.Generates w) : H.Generates w := by
  simpa [Grammar.freeze] using h.preserves_frozen_word (F := ∅) (by simp) w
    (by simpa [Grammar.freeze] using hw)

end GlobalStep

end GreedyLowerBound
