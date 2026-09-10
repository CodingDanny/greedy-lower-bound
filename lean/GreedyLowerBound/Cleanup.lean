import GreedyLowerBound.GlobalCompetitors

set_option autoImplicit false

namespace GreedyLowerBound

theorem Packing.factor_isInfix {α : Type} {v w : Word α} {c : Nat}
    (h : Packing v w c) (hc : 0 < c) : v.IsInfix w := by
  cases h with
  | zero => omega
  | next pre rest ht => exact ⟨pre, rest, by simp [List.append_assoc]⟩

theorem NoAdjacent.of_infix {X : Nat} {v w : Word Nat}
    (hw : NoAdjacent X w) (hv : v.IsInfix w) : NoAdjacent X v :=
  fun hh => hw (hh.trans hv)

theorem noAdjacent_cons_iff (X a : Nat) (w : Word Nat) :
    NoAdjacent X (a::w) ↔ (a = X → ¬ [X].IsPrefix w) ∧ NoAdjacent X w := by
  simp only [NoAdjacent, List.infix_cons_iff, List.cons_prefix_cons, not_or,
    not_and]
  constructor
  · rintro ⟨h, hw⟩
    exact ⟨fun he => h he.symm, hw⟩
  · rintro ⟨h, hw⟩
    exact ⟨fun he => h he.symm, hw⟩

/-- A scan using a different fresh symbol cannot introduce X at the front. -/
theorem Scan.old_prefix_of_new_prefix {v s t : Word Nat} {fresh X c : Nat}
    (h : Scan v fresh s t c) (hf : fresh ≠ X) (ht : [X].IsPrefix t) :
    [X].IsPrefix s := by
  cases h with
  | nil => simp at ht
  | hit h =>
    have he := (List.cons_prefix_cons.mp ht).1
    exact False.elim (hf he.symm)
  | skip hn h =>
    have he := (List.cons_prefix_cons.mp ht).1
    exact List.cons_prefix_cons.mpr ⟨he, List.nil_prefix⟩

/-- The exact adjacency assertion used for finished-auxiliary cleanup in
Section 4.5, for arbitrary nonempty factors and arbitrary scan positions. -/
theorem Scan.preserves_noAdjacent {v s t : Word Nat} {fresh X c : Nat}
    (h : Scan v fresh s t c) (hf : fresh ≠ X) (hs : NoAdjacent X s) :
    NoAdjacent X t := by
  induction h with
  | nil => exact hs
  | @hit s t c h ih =>
    have htail : NoAdjacent X s := hs.of_infix (List.suffix_append _ _).isInfix
    exact (noAdjacent_cons_iff X fresh t).mpr ⟨fun he => False.elim (hf he), ih htail⟩
  | @skip a s t c hn h ih =>
    have hh := (noAdjacent_cons_iff X a s).mp hs
    refine (noAdjacent_cons_iff X a t).mpr ⟨?_, ih hh.2⟩
    intro he hp
    exact hh.1 he (h.old_prefix_of_new_prefix hf hp)

/-- The fresh definition also satisfies the old no-adjacency invariant. -/
theorem Scan.new_rule_noAdjacent {v s t : Word Nat} {fresh X c : Nat}
    (h : Scan v fresh s t c) (hc : 0 < c) (hs : NoAdjacent X s) :
    NoAdjacent X v := hs.of_infix (h.packing.factor_isInfix hc)

/-- A length-at-least-two factor in finished auxiliary storage must contain
something other than that storage's one primary symbol. -/
theorem NoAdjacent.factor_has_other {X : Nat} {v w : Word Nat}
    (hw : NoAdjacent X w) (hv : v.IsInfix w) (hlen : 2 ≤ v.length) :
    ∃ a ∈ v, a ≠ X := by
  by_contra h
  have hall : ∀ a ∈ v, a = X := by
    intro a ha
    by_contra he
    exact h ⟨a, ha, he⟩
  have he : v = List.replicate v.length X := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
  have hh : [X, X].IsInfix v := by
    rw [he]
    have hl : v.length = 2+(v.length-2) := by omega
    rw [hl, List.replicate_add]
    exact (List.prefix_append _ _).isInfix
  exact hw (hh.trans hv)

/-- Literal ownership is preserved by replacing within a class and assigning
the newly created symbol to that same class. -/
theorem Scan.preserves_alphabet {v s t : Word Nat} {fresh c : Nat}
    (h : Scan v fresh s t c) (A : Nat → Prop) (hs : ∀ a ∈ s, A a) :
    ∀ a ∈ t, a = fresh ∨ A a := by
  intro a ha
  rcases h.output_mem a ha with he | hm
  · exact Or.inl he
  · exact Or.inr (hs a hm)

theorem Scan.new_rule_alphabet {v s t : Word Nat} {fresh c : Nat}
    (h : Scan v fresh s t c) (hc : 0 < c) (A : Nat → Prop)
    (hs : ∀ a ∈ s, A a) : ∀ a ∈ v, A a := by
  intro a ha
  exact hs a (h.factor_mem_of_positive hc a ha)

/-- Cells outside a private symbol's class are literally unchanged. -/
theorem Scan.unchanged_of_private_absent {v s t : Word Nat} {fresh c : Nat}
    (h : Scan v fresh s t c) (a : Nat) (ha : a ∈ v) (hs : a ∉ s) : s = t := by
  apply h.zero_eq
  by_contra hc
  exact hs (h.factor_mem_of_positive (by omega) a ha)

/-- Marker-bearing old private symbols produce marker-bearing new symbols
under the frozen interpretation. -/
theorem flatMap_contains_marker (value : Nat → Word Nat) (markers : Nat → Prop)
    (v : Word Nat) (a : Nat) (ha : a ∈ v)
    (hm : ∃ z ∈ value a, markers z) :
    ∃ z ∈ v.flatMap value, markers z := by
  obtain ⟨z, hz, hp⟩ := hm
  exact ⟨z, List.mem_flatMap.mpr ⟨a, ha, hz⟩, hp⟩

/-- A power-layer factor containing at least two symbols has frozen expansion
length at least two, provided every old symbol expands nonemptily. -/
theorem flatMap_length_ge (value : Nat → Word Nat) (v : Word Nat)
    (hv : ∀ a ∈ v, value a ≠ []) : v.length ≤ (v.flatMap value).length := by
  induction v with
  | nil => simp
  | cons a v ih =>
    have ha := List.length_pos_iff.mpr (hv a (by simp))
    have ht := ih (fun a ha => hv a (by simp [ha]))
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

theorem flatMap_unary (value : Nat → Word Nat) (v : Word Nat) (X : Nat)
    (hv : ∀ a ∈ v, ∀ b ∈ value a, b = X) :
    v.flatMap value = List.replicate (v.flatMap value).length X := by
  apply List.eq_replicate_iff.mpr
  refine ⟨rfl, ?_⟩
  intro b hb
  obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hb
  exact hv a ha b hb

end GreedyLowerBound
