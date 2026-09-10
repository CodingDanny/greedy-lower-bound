import GreedyLowerBound.Ownership

set_option autoImplicit false

namespace GreedyLowerBound

def binaryCode (b : Bool) : List Bool := [b, !b]
def binaryEncode (w : List Bool) : List Bool := w.flatMap binaryCode

theorem binaryEncode_length (w : List Bool) : (binaryEncode w).length = 2*w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [binaryEncode, List.flatMap_cons, binaryCode, List.length_append,
      List.length_cons, List.length_nil] at *
    omega

/-- Chunk s uses h consecutive source bits. Encoding this source slice makes
the code alignment of every chunk explicit. Indices here are zero based. -/
def chunk (h : Nat) (D : List Bool) (s : Nat) : List Bool :=
  binaryEncode ((D.drop (s*h)).take h)

theorem chunk_source_length (h : Nat) (D : List Bool) (s : Nat)
    (hD : D.length = h^2) (hs : s < h) : ((D.drop (s*h)).take h).length = h := by
  have hm := Nat.mul_le_mul_right h (show s+1 ≤ h by omega)
  simp only [Nat.add_mul, Nat.one_mul] at hm
  simp only [List.length_take, List.length_drop, hD, Nat.pow_two]
  omega

theorem chunk_length (h : Nat) (D : List Bool) (s : Nat)
    (hD : D.length = h^2) (hs : s < h) : (chunk h D s).length = 2*h := by
  rw [chunk, binaryEncode_length, chunk_source_length h D s hD hs]

theorem binaryValue_positive (B : Nat) (hB : 0 < B) (w : List Bool)
    (hw : true ∈ w) : 0 < binaryValue B w := by
  induction w with
  | nil => simp at hw
  | cons b w ih =>
    rcases List.mem_cons.mp hw with hb | hw
    · subst b
      have hp := Nat.pow_pos (n := w.length) hB
      simp only [binaryValue, if_true, Nat.one_mul]
      omega
    · have ht := ih hw
      simp only [binaryValue]
      omega

theorem binaryEncode_prefix_has_one (w : List Bool) (n : Nat) (hw : w ≠ [])
    (hn : 2 ≤ n) : true ∈ (binaryEncode w).take n := by
  cases w with
  | nil => contradiction
  | cons b w =>
    have hn' : n = 2+(n-2) := by omega
    rw [hn']
    simp only [binaryEncode, List.flatMap_cons, binaryCode]
    rw [List.take_append_eq_append_take]
    rw [List.take_of_length_le (by simp : [b, !b].length ≤ 2+(n-2))]
    cases b <;> simp

def targetNumber (h : Nat) (D : List Bool) (s i : Nat) : Nat :=
  binaryValue 64 ((chunk h D s).take (h+1+i))

def targetNumbers (h : Nat) (D : List Bool) : List Nat :=
  (List.range h).flatMap (fun s => (List.range h).map (fun i => targetNumber h D s i))

theorem targetNumber_positive (h : Nat) (D : List Bool) (s i : Nat)
    (hh : 1 ≤ h) (hD : D.length = h^2) (hs : s < h) :
    0 < targetNumber h D s i := by
  have hlen := chunk_source_length h D s hD hs
  apply binaryValue_positive 64 (by decide)
  apply binaryEncode_prefix_has_one
  · intro he
    simp only [he, List.length_nil] at hlen
    omega
  · omega

theorem targetNumber_lt (h : Nat) (D : List Bool) (s i : Nat)
    (hD : D.length = h^2) (hs : s < h) : targetNumber h D s i < 64^(2*h) := by
  have hv := binaryValue_lt 64 (by decide) ((chunk h D s).take (h+1+i))
  have hl : ((chunk h D s).take (h+1+i)).length ≤ 2*h := by
    rw [List.length_take, chunk_length h D s hD hs]
    exact Nat.min_le_right _ _
  exact hv.trans_le (Nat.pow_le_pow_right (by decide) hl)

theorem targetNumbers_length (h : Nat) (D : List Bool) :
    (targetNumbers h D).length = h^2 := by
  simp [targetNumbers, List.length_flatMap, List.map_map, Function.comp_def,
    List.map_const', Nat.pow_two]

theorem targetNumbers_mem (h : Nat) (D : List Bool) (n : Nat)
    (hn : n ∈ targetNumbers h D) : ∃ s < h, ∃ i < h, n = targetNumber h D s i := by
  obtain ⟨s, hs, hn⟩ := List.mem_flatMap.mp hn
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hn
  exact ⟨s, List.mem_range.mp hs, i, List.mem_range.mp hi, he.symm⟩

theorem targetNumbers_positive (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) (n : Nat) (hn : n ∈ targetNumbers h D) : 0 < n := by
  obtain ⟨s, hs, i, hi, rfl⟩ := targetNumbers_mem h D n hn
  exact targetNumber_positive h D s i hh hD hs

theorem sum_le_length_mul (w : List Nat) (B : Nat) (hw : ∀ n ∈ w, n ≤ B) :
    w.sum ≤ w.length*B := by
  induction w with
  | nil => simp
  | cons n w ih =>
    have hn := hw n (by simp)
    have ht := ih (fun m hm => hw m (by simp [hm]))
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem targetNumbers_sum_le (h : Nat) (D : List Bool) (hD : D.length = h^2) :
    (targetNumbers h D).sum ≤ targetMass h := by
  have hh := sum_le_length_mul (targetNumbers h D) (64^(2*h)) (by
    intro n hn
    obtain ⟨s, hs, i, hi, rfl⟩ := targetNumbers_mem h D n hn
    exact Nat.le_of_lt (targetNumber_lt h D s i hD hs))
  simpa only [targetNumbers_length, targetMass] using hh

theorem targetNumber_digits (h : Nat) (D : List Bool) (s i u : Nat) :
    baseDigit (targetNumber h D s i) u ≤ 1 := binaryValue_digits _ u

/-- Three distinct markers per zero-based auxiliary index. Terminal a is 0. -/
def markerName (j : Nat) (c : Letter) : Nat := 1+3*j+c.val

def auxiliaryAlphabet (X j : Nat) : Option Letter → Nat
  | none => X
  | some c => markerName j c

theorem markerName_injective {j k : Nat} {a b : Letter}
    (he : markerName j a = markerName k b) : j = k ∧ a = b := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [markerName] at he
  have hj : j = k := by omega
  refine ⟨hj, Fin.ext ?_⟩
  omega

theorem auxiliaryAlphabet_injective (X j : Nat)
    (hX : ∀ c : Letter, X ≠ markerName j c) : Function.Injective (auxiliaryAlphabet X j) := by
  intro a b he
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => exact False.elim (hX b he)
  | some a =>
    cases b with
    | none => exact False.elim (hX a he.symm)
    | some b => exact congrArg some (markerName_injective he).2

def inputAuxiliary (h j : Nat) : Word Nat :=
  (auxiliaryWord (64^(j+1)) (muIterate (auxiliaryExponent h (j+1)))).map
    (auxiliaryAlphabet 0 j)

theorem inputAuxiliary_length (h j : Nat) :
    (inputAuxiliary h j).length = auxiliaryLength h (j+1)*(64^(j+1)+1) := by
  simp [inputAuxiliary, auxiliaryWord_length, muIterate_length, auxiliaryLength]

theorem inputAuxiliary_nonempty (h j : Nat) : inputAuxiliary h j ≠ [] := by
  apply List.length_pos_iff.mp
  rw [inputAuxiliary_length]
  apply Nat.mul_pos
  · exact Nat.pow_pos (by decide)
  · exact Nat.zero_lt_succ _

end GreedyLowerBound
