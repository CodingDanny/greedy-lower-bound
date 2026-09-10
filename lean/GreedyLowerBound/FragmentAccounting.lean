import GreedyLowerBound.FragmentScans
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List

set_option autoImplicit false

namespace GreedyLowerBound

/-- Literal storage cells: all start-rule fragments and every non-start
right-hand side. No cell is omitted from the global frequency calculation. -/
structure Fragmentation (G : Grammar) where
  first : Word Nat
  rest : List (Nat × Word Nat)
  start_mem : G.start ∈ G.defined
  start_eq : G.rhs G.start = joinFragments first rest
  separators : ∀ p ∈ rest, G.StartSeparator p.1

namespace Fragmentation

noncomputable def pieces {G : Grammar} (P : Fragmentation G) : List (Word Nat) :=
  (P.first :: P.rest.map Prod.snd) ++ (G.defined.erase G.start).toList.map G.rhs

theorem piece_in_rhs {G : Grammar} (P : Fragmentation G) (w : Word Nat)
    (hw : w ∈ P.pieces) : ∃ i ∈ G.defined, w.IsInfix (G.rhs i) := by
  rcases List.mem_append.mp hw with hw | hw
  · refine ⟨G.start, P.start_mem, ?_⟩
    rw [P.start_eq]
    rcases List.mem_cons.mp hw with hw | hw
    · subst w
      exact (List.prefix_append _ _).isInfix
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
      obtain ⟨left, right, he⟩ := List.append_of_mem hp
      refine ⟨P.first ++ left.flatMap (fun p => p.1 :: p.2) ++ [p.1],
        right.flatMap (fun p => p.1 :: p.2), ?_⟩
      simp [joinFragments, he, List.flatMap_append, List.append_assoc]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact ⟨i, (Finset.mem_erase.mp (Finset.mem_toList.mp hi)).2, List.infix_refl _⟩

theorem frequency_eq {G : Grammar} (P : Fragmentation G)
    (v : Word Nat) (hv : G.Eligible v) :
    G.frequency v = (P.pieces.map (scanCount v)).sum := by
  have hvn : v ≠ [] := by intro he; have hh := hv.1; simp [he] at hh
  have hz : ∀ p ∈ P.rest, p.1 ∉ v := by
    intro p hp
    exact G.eligible_excludes_single_symbol v p.1 hv
      (by rw [(P.separators p hp).symbolCount])
  have hs := scanCount_joinFragments v P.first P.rest hvn hz
  rw [← P.start_eq] at hs
  unfold Grammar.frequency
  rw [← Finset.sum_erase_add _ _ P.start_mem, hs]
  simp [pieces, List.sum_append, Finset.sum_map_toList, List.map_map, Function.comp_def,
    Nat.add_comm, Nat.add_left_comm]

theorem eligible_occurs_piece {G : Grammar} (P : Fragmentation G) (v : Word Nat)
    (hv : G.Eligible v) : ∃ w ∈ P.pieces, 0 < scanCount v w := by
  by_contra hn
  have hz : (P.pieces.map (scanCount v)).sum = 0 := by
    apply List.sum_eq_zero
    intro n hn'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hn'
    by_contra hc
    exact hn ⟨w, hw, by omega⟩
  have he := P.frequency_eq v hv
  have hh := hv.2
  omega

end Fragmentation

theorem Packing.append {α : Type} {v w : Word α} {c : Nat}
    (h : Packing v w c) (tail : Word α) : Packing v (w ++ tail) c := by
  induction h with
  | zero => exact Packing.zero _
  | next pre rest h ih =>
    simpa only [List.append_assoc] using Packing.next pre (rest ++ tail) ih

theorem scanCount_le_of_infix (v w s : Word Nat) (hv : v ≠ []) (hw : w.IsInfix s) :
    scanCount v w ≤ scanCount v s := by
  obtain ⟨pre, post, rfl⟩ := hw
  have hp := ((scanCount_is_maximum v w hv).1.append post).prepend pre
  exact (scanCount_is_maximum v _ hv).2 _ (by simpa only [List.append_assoc] using hp)

theorem Fragmentation.scanCount_le_frequency {G : Grammar} (P : Fragmentation G)
    (v w : Word Nat) (hv : v ≠ []) (hw : w ∈ P.pieces) :
    scanCount v w ≤ G.frequency v := by
  obtain ⟨i, hi, hh⟩ := P.piece_in_rhs w hw
  have hl := scanCount_le_of_infix v w (G.rhs i) hv hh
  have hs := Finset.single_le_sum (f := fun j => scanCount v (G.rhs j))
    (fun j _ => Nat.zero_le _) hi
  exact hl.trans hs

theorem Packing.covered_length_le {α : Type} {v w : Word α} {c : Nat}
    (h : Packing v w c) : c * v.length ≤ w.length := by
  induction h with
  | zero => simp
  | next pre rest h ih =>
    simp only [List.length_append, Nat.add_mul, Nat.one_mul]
    omega

theorem scanCount_covered_length_le (v w : Word Nat) :
    scanCount v w * v.length ≤ w.length := by
  by_cases hv : v = []
  · simp [hv]
  · exact (scanCount_is_maximum v w hv).1.covered_length_le

theorem scanCount_zero_of_missing (v w : Word Nat) (a : Nat)
    (ha : a ∈ v) (hw : a ∉ w) : scanCount v w = 0 := by
  by_contra hc
  have hv : v ≠ [] := by intro he; simp [he] at ha
  obtain ⟨t, ht⟩ := Scan.exists_output v w a hv
  exact hw (ht.factor_mem_of_positive (by omega) a ha)

/-- Sum of maximum disjoint occurrence counts over a list of literal cells. -/
def cellFrequency (cells : List (Word Nat)) (v : Word Nat) : Nat :=
  (cells.map (scanCount v)).sum

def cellMass (cells : List (Word Nat)) : Nat := (cells.map List.length).sum

theorem cellFrequency_append (a b : List (Word Nat)) (v : Word Nat) :
    cellFrequency (a ++ b) v = cellFrequency a v + cellFrequency b v := by
  simp [cellFrequency]

theorem cellFrequency_covered_length_le (cells : List (Word Nat)) (v : Word Nat) :
    cellFrequency cells v * v.length ≤ cellMass cells := by
  induction cells with
  | nil => simp [cellFrequency, cellMass]
  | cons w cells ih =>
    have hw := scanCount_covered_length_le v w
    simp only [cellFrequency, cellMass, List.map_cons, List.sum_cons] at *
    rw [Nat.add_mul]
    omega

theorem cellFrequency_single_le (cells : List (Word Nat)) (v w : Word Nat)
    (hw : w ∈ cells) : scanCount v w ≤ cellFrequency cells v := by
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨w, hw, rfl⟩)

theorem cellFrequency_zero_of_missing (cells : List (Word Nat)) (v : Word Nat) (a : Nat)
    (ha : a ∈ v) (hc : ∀ w ∈ cells, a ∉ w) : cellFrequency cells v = 0 := by
  unfold cellFrequency
  apply List.sum_eq_zero
  intro n hn
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hn
  exact scanCount_zero_of_missing v w a ha (hc w hw)

/-- A marker with a unique owner confines the global count to that owner's
cell. The cells are supplied explicitly, so no other rules are ignored. -/
theorem cellFrequency_confined (left right : List (Word Nat)) (owner v : Word Nat)
    (a : Nat) (ha : a ∈ v)
    (hl : ∀ w ∈ left, a ∉ w) (hr : ∀ w ∈ right, a ∉ w) :
    cellFrequency (left ++ owner :: right) v = scanCount v owner := by
  rw [cellFrequency_append, cellFrequency_zero_of_missing left v a ha hl]
  change 0 + (scanCount v owner + cellFrequency right v) = _
  rw [cellFrequency_zero_of_missing right v a ha hr]
  omega

/-- If all occurrences are in bounded target storage, their total covered
length bounds the grammar-wide gain. -/
theorem Grammar.gain_le_mass_of_frequency {G : Grammar} (v : Word Nat)
    (cells : List (Word Nat)) (hf : G.frequency v = cellFrequency cells v) :
    G.gain v ≤ cellMass cells := by
  have hb := cellFrequency_covered_length_le cells v
  have hb' := Int.ofNat_le.mpr hb
  dsimp [Grammar.gain]
  rw [hf]
  push_cast at hb'
  have hc : (0 : Int) ≤ cellFrequency cells v := Int.natCast_nonneg _
  have hl : (0 : Int) ≤ v.length := Int.natCast_nonneg _
  nlinarith

end GreedyLowerBound
