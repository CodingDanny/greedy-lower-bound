import GreedyLowerBound.ScanCount
import GreedyLowerBound.PackingSpacing
import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace GreedyLowerBound

variable {α : Type} {s t : Word α} {c : Nat}

theorem Scan.prepend_unary_blocks (B q : Nat) (X Y : α)
    (h : Scan (List.replicate B X) Y s t c) :
    Scan (List.replicate B X) Y (List.replicate (q*B) X ++ s)
      (List.replicate q Y ++ t) (q+c) := by
  induction q with
  | zero => simpa using h
  | succ q ih =>
    have hh := Scan.hit ih
    have he : (q+1)*B = B+q*B := by simp [Nat.add_mul, Nat.add_comm]
    simpa only [he, List.replicate_add, List.append_assoc, List.replicate_succ,
      List.cons_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem Scan.unary_remainder (B r : Nat) (X Y : α) (hr : r < B) :
    Scan (List.replicate B X) Y (List.replicate r X) (List.replicate r X) 0 := by
  induction r with
  | zero => exact Scan.nil
  | succ r ih =>
    have hn : ¬ (List.replicate B X).IsPrefix (X::List.replicate r X) := by
      intro hp
      have hh := hp.length_le
      simp only [List.length_replicate, List.length_cons] at hh
      omega
    exact Scan.skip hn (ih (by omega))

/-- Exact quotient/remainder behavior of a left-to-right unary substitution. -/
theorem Scan.unary_division (B n : Nat) (X Y : α) (hB : 0 < B) :
    Scan (List.replicate B X) Y (List.replicate n X)
      (List.replicate (n/B) Y ++ List.replicate (n%B) X) (n/B) := by
  have hr := Scan.unary_remainder B (n%B) X Y (Nat.mod_lt n hB)
  have hh := hr.prepend_unary_blocks B (n/B) X Y
  have he : n/B*B+n%B = n := by simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div n B
  simpa only [← List.replicate_add, he, Nat.add_zero] using hh

theorem scanCount_replicate [DecidableEq α] (B n : Nat) (X : α) (hB : 0 < B) :
    scanCount (List.replicate B X) (List.replicate n X) = n/B := by
  have h := Scan.unary_division B n X X hB
  have hv : List.replicate B X ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [List.length_replicate, List.length_nil] at hh
    omega
  exact (h.count_eq hv).symm

theorem unary_prefix_blocked (B r : Nat) (X z : α) (w : Word α)
    (hr : r < B) (hz : z ≠ X) :
    ¬ (List.replicate B X).IsPrefix (List.replicate r X ++ (z::w)) := by
  intro hp
  have he := prefix_drop_get (List.replicate B X) (List.replicate r X ++ (z::w))
    0 (by simpa using hp) r (by simpa using hr)
  simp only [Nat.zero_add, List.getElem?_append_right (by simp :
      (List.replicate r X).length ≤ r), List.length_replicate, Nat.sub_self,
    List.getElem?_cons_zero, List.getElem?_replicate_of_lt hr, Option.some.injEq] at he
  exact hz he

/-- A short remainder followed by a different symbol is copied literally; the
tail may itself undergo further substitutions. -/
theorem Scan.prepend_unary_remainder (B r : Nat) (X Y z : α) (hz : z ≠ X)
    (hr : r < B) (h : Scan (List.replicate B X) Y s t c) :
    Scan (List.replicate B X) Y (List.replicate r X ++ (z::s))
      (List.replicate r X ++ (z::t)) c := by
  induction r with
  | zero =>
    have hn := unary_prefix_blocked B 0 X z s (by omega) hz
    simpa using Scan.skip (by simpa using hn) h
  | succ r ih =>
    have hn := unary_prefix_blocked B (r+1) X z s hr hz
    simpa only [List.replicate_succ, List.cons_append] using
      Scan.skip (by simpa only [List.replicate_succ, List.cons_append] using hn) (ih (by omega))

/-- Exact run substitution with a marker boundary. This prevents any hidden
interaction between a remainder and the following fragment. -/
theorem Scan.unary_division_before_marker (B n : Nat) (X Y z : α)
    (hB : 0 < B) (hz : z ≠ X) (h : Scan (List.replicate B X) Y s t c) :
    Scan (List.replicate B X) Y (List.replicate n X ++ (z::s))
      (List.replicate (n/B) Y ++ (List.replicate (n%B) X ++ (z::t))) (n/B+c) := by
  have hr := h.prepend_unary_remainder B (n%B) X Y z hz (Nat.mod_lt n hB)
  have hh := hr.prepend_unary_blocks B (n/B) X Y
  have he : n/B*B+n%B = n := by simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div n B
  simpa only [← List.append_assoc, ← List.replicate_add, he] using hh

/-- A padded marker word with divisible run lengths is transformed exactly
into the padded word over the new symbol. -/
theorem Scan.padded_word (B k : Nat) (X Y : α) (w : Word α) (hB : 0 < B)
    (hw : ∀ z ∈ w, z ≠ X) :
    Scan (List.replicate B X) Y
      (w.flatMap fun z => List.replicate (k*B) X ++ [z])
      (w.flatMap fun z => List.replicate k Y ++ [z]) (w.length*k) := by
  induction w with
  | nil => simpa using (Scan.nil (v := List.replicate B X) (fresh := Y))
  | cons z w ih =>
    have ht := ih (fun a ha => hw a (by simp [ha]))
    have hz := hw z (by simp)
    have hn := unary_prefix_blocked B 0 X z
      (w.flatMap fun a => List.replicate (k*B) X ++ [a]) (by omega) hz
    have hs := Scan.skip (by simpa using hn) ht
    have hh := hs.prepend_unary_blocks B k X Y
    simpa only [List.flatMap_cons, List.append_assoc, List.singleton_append,
      List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using hh

end GreedyLowerBound
