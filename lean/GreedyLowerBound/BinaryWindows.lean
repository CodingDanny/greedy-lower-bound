import GreedyLowerBound.Construction
import GreedyLowerBound.Slices
import Mathlib.Data.Finset.Card

set_option autoImplicit false
namespace GreedyLowerBound

/-- Linear uniqueness of length-q windows. A cyclic binary de Bruijn word,
cut at any position, supplies this property; its existence is separate. -/
def UniqueWindows (w : List Bool) (q : Nat) : Prop :=
  ∀ a b, a+q ≤ w.length → b+q ≤ w.length → EqualIntervals w a b q → a = b

theorem binaryEncode_get_even (w : List Bool) (k : Nat) :
    (binaryEncode w)[2*k]? = w[k]? := by
  induction w generalizing k with
  | nil => simp [binaryEncode]
  | cons b w ih =>
    cases k with
    | zero => simp [binaryEncode, binaryCode]
    | succ k =>
      simpa only [binaryEncode, List.flatMap_cons, binaryCode, List.cons_append,
        List.nil_append, Nat.mul_succ, List.getElem?_cons_succ] using ih k

theorem binaryEncode_drop (w : List Bool) (k : Nat) :
    binaryEncode (w.drop k) = (binaryEncode w).drop (2*k) := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    cases w with
    | nil => simp [binaryEncode]
    | cons b w =>
      simpa only [List.drop_succ_cons, binaryEncode, List.flatMap_cons, binaryCode,
        List.cons_append, List.nil_append, Nat.mul_succ, List.drop_succ_cons] using ih w

theorem binaryEncode_take (w : List Bool) (k : Nat) :
    binaryEncode (w.take k) = (binaryEncode w).take (2*k) := by
  induction k generalizing w with
  | zero => simp [binaryEncode]
  | succ k ih =>
    cases w with
    | nil => simp [binaryEncode]
    | cons b w =>
      simpa only [List.take_succ_cons, binaryEncode, List.flatMap_cons, binaryCode,
        List.cons_append, List.nil_append, Nat.mul_succ, List.take_succ_cons, Function.comp_def] using congrArg (List.cons b ∘ List.cons (!b)) (ih w)

/-- The separately defined chunks are literal aligned slices of the one
encoded seed. This fixes the position correspondence needed for reconstruction. -/
theorem chunk_eq_slice (h : Nat) (D : List Bool) (s : Nat) :
    chunk h D s = slice (binaryEncode D) (2*h*s) (2*h) := by
  rw [chunk, binaryEncode_take, binaryEncode_drop]
  unfold slice
  congr 2
  ac_rfl

/-- Equal encoded factors of the same parity expose equal q-letter source
windows. Bounds include factors at either end of the finite word. -/
theorem encoded_same_parity_start (D : List Bool) (q L a b : Nat)
    (hD : UniqueWindows D q) (hL : 2*q+2 ≤ L)
    (ha : a+L ≤ (binaryEncode D).length) (hb : b+L ≤ (binaryEncode D).length)
    (hp : a%2 = b%2) (he : EqualIntervals (binaryEncode D) a b L) : a = b := by
  rw [binaryEncode_length] at ha hb
  let i := (a+1)/2
  let j := (b+1)/2
  have hi : i+q ≤ D.length := by dsimp [i]; omega
  have hj : j+q ≤ D.length := by dsimp [j]; omega
  have hij : i = j := hD i j hi hj (by
    intro k hk
    have hk' : a%2+2*k < L := by omega
    have hh := he (a%2+2*k) hk'
    have hae : a+(a%2+2*k) = 2*(i+k) := by dsimp [i]; omega
    have hbe : b+(a%2+2*k) = 2*(j+k) := by dsimp [j]; omega
    rw [hae, hbe, binaryEncode_get_even, binaryEncode_get_even] at hh
    exact hh)
  dsimp [i, j] at hij
  omega

/-- In any finite collection of equal long encoded factors, reduction of
start position modulo two is injective. -/
theorem encoded_starts_mod_two_injective (D : List Bool) (q L : Nat)
    (hD : UniqueWindows D q) (hL : 2*q+2 ≤ L) (starts : Finset Nat)
    (hb : ∀ a ∈ starts, a+L ≤ (binaryEncode D).length)
    (he : ∀ a ∈ starts, ∀ b ∈ starts, EqualIntervals (binaryEncode D) a b L) :
    Set.InjOn (fun a => a%2) (↑starts : Set Nat) := by
  intro a ha b hb' hp
  exact encoded_same_parity_start D q L a b hD hL (hb a ha) (hb b hb') hp (he a ha b hb')

/-- The multiplicity bound in Section 6, expressed without a choice of
representative occurrence or a hidden injectivity assumption. -/
theorem encoded_factor_multiplicity (D : List Bool) (q L : Nat)
    (hD : UniqueWindows D q) (hL : 2*q+2 ≤ L) (starts : Finset Nat)
    (hb : ∀ a ∈ starts, a+L ≤ (binaryEncode D).length)
    (he : ∀ a ∈ starts, ∀ b ∈ starts, EqualIntervals (binaryEncode D) a b L) :
    starts.card ≤ 2 := by
  have hc : starts.card ≤ (Finset.range 2).card :=
    Finset.card_le_card_of_injOn (fun a => a%2)
      (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ (by decide)))
      (encoded_starts_mod_two_injective D q L hD hL starts hb he)
  simpa using hc

end GreedyLowerBound
