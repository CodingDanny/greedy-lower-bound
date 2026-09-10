import GreedyLowerBound.ActiveCleanup

set_option autoImplicit false

namespace GreedyLowerBound

/-- Most-significant-digit-first value. Only binary digits are used in the
construction, even though the arithmetic base is 64. -/
def binaryValue (B : Nat) : List Bool → Nat
  | [] => 0
  | b :: w => (if b then 1 else 0) * B^w.length + binaryValue B w

theorem binaryValue_lt (B : Nat) (hB : 2 ≤ B) (w : List Bool) :
    binaryValue B w < B^w.length := by
  induction w with
  | nil => simp [binaryValue]
  | cons b w ih =>
    have hpow : 0 < B^w.length := Nat.pow_pos (by omega)
    have hm := Nat.mul_le_mul_left (B^w.length) hB
    cases b <;> simp only [binaryValue, Bool.false_eq_true, if_false, if_true,
      Nat.zero_mul, Nat.one_mul, Nat.zero_add, List.length_cons, Nat.pow_succ] <;> omega

theorem binaryValue_append (B : Nat) (v w : List Bool) :
    binaryValue B (v++w) = binaryValue B v * B^w.length + binaryValue B w := by
  induction v with
  | nil => simp [binaryValue]
  | cons b v ih =>
    simp only [List.cons_append, binaryValue, List.length_append, Nat.pow_add, ih]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

theorem binaryValue_div (B : Nat) (hB : 2 ≤ B) (v w : List Bool) :
    binaryValue B (v++w) / B^w.length = binaryValue B v := by
  rw [binaryValue_append]
  have hp : 0 < B^w.length := Nat.pow_pos (by omega)
  have hsmall := binaryValue_lt B hB w
  rw [Nat.mul_comm (binaryValue B v) (B^w.length), Nat.mul_add_div hp,
    Nat.div_eq_of_lt hsmall, Nat.add_zero]

theorem binaryValue_mod (B : Nat) (hB : 2 ≤ B) (v w : List Bool) :
    binaryValue B (v++w) % B^w.length = binaryValue B w := by
  rw [binaryValue_append, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
    Nat.mod_mod, Nat.mod_eq_of_lt (binaryValue_lt B hB w)]

/-- The arithmetic base-64 digit at position u, counted from the right. -/
def baseDigit (n u : Nat) : Nat := n / 64^u % 64

theorem binaryValue_digits (w : List Bool) (u : Nat) :
    baseDigit (binaryValue 64 w) u ≤ 1 := by
  induction w with
  | nil => simp [baseDigit, binaryValue]
  | cons b w ih =>
    by_cases hu : u < w.length
    · have hpow : 64^w.length = 64^u * 64^(w.length-u) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      have hp : 0 < 64^u := Nat.pow_pos (by decide)
      have he : w.length-u = (w.length-u-1)+1 := by omega
      unfold baseDigit
      simp only [binaryValue]
      rw [hpow, ← Nat.mul_assoc, Nat.mul_comm (if b then 1 else 0) (64^u),
        Nat.mul_assoc, Nat.mul_add_div hp]
      rw [Nat.add_mod]
      have hz : ((if b then 1 else 0)*64^(w.length-u)) % 64 = 0 := by
        rw [he, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_mod_left]
      rw [hz, Nat.zero_add, Nat.mod_mod]
      exact ih
    · by_cases he : u = w.length
      · subst u
        unfold baseDigit
        rw [binaryValue, Nat.mul_comm (if b then 1 else 0) (64^w.length),
          Nat.mul_add_div (Nat.pow_pos (by decide : 0 < 64)),
          Nat.div_eq_of_lt (binaryValue_lt 64 (by decide) w), Nat.add_zero]
        cases b <;> decide
      · have hlu : w.length+1 ≤ u := by omega
        have hlt := binaryValue_lt 64 (by decide) (b::w)
        have hpow := Nat.pow_le_pow_right (by decide : 0 < 64) hlu
        have hzero : binaryValue 64 (b::w) / 64^u = 0 :=
          Nat.div_eq_of_lt (hlt.trans_le hpow)
        simp [baseDigit, hzero]

/-- Frozen lower primary digits, listed in decreasing primary index. -/
def lowerDigits (n : Nat) (A : Nat → Nat) : Nat → Word Nat
  | 0 => []
  | t+1 => List.replicate (baseDigit n t) (A t) ++ lowerDigits n A t

def targetState (n : Nat) (A : Nat → Nat) (t : Nat) : Word Nat :=
  List.replicate (n/64^t) (A t) ++ lowerDigits n A t

theorem lowerDigits_mem (n : Nat) (A : Nat → Nat) (t : Nat) (a : Nat)
    (ha : a ∈ lowerDigits n A t) : ∃ u < t, a = A u := by
  induction t with
  | zero => simp [lowerDigits] at ha
  | succ t ih =>
    rcases List.mem_append.mp ha with ha | ha
    · exact ⟨t, by omega, (List.mem_replicate.mp ha).2⟩
    · obtain ⟨u, hu, he⟩ := ih ha
      exact ⟨u, by omega, he⟩

theorem lowerDigits_avoids_active (n : Nat) (A : Nat → Nat) (t : Nat)
    (hA : Function.Injective A) : A t ∉ lowerDigits n A t := by
  intro hm
  obtain ⟨u, hu, he⟩ := lowerDigits_mem n A t (A t) hm
  have hh := hA he
  omega

theorem lowerDigits_nodup (n : Nat) (A : Nat → Nat) (t : Nat)
    (hA : Function.Injective A) (hd : ∀ u < t, baseDigit n u ≤ 1) :
    (lowerDigits n A t).Nodup := by
  induction t with
  | zero => simp [lowerDigits]
  | succ t ih =>
    have ht := ih (fun u hu => hd u (by omega))
    have hb := hd t (by omega)
    have ha := lowerDigits_avoids_active n A t hA
    have he : baseDigit n t = 0 ∨ baseDigit n t = 1 := by omega
    rcases he with he | he
    · simpa [lowerDigits, he] using ht
    · simpa [lowerDigits, he] using List.nodup_cons.mpr ⟨ha, ht⟩

theorem targetState_other_count (n : Nat) (A : Nat → Nat) (t a : Nat)
    (hA : Function.Injective A) (hd : ∀ u < t, baseDigit n u ≤ 1)
    (ha : a ≠ A t) : (targetState n A t).count a ≤ 1 := by
  have hn := lowerDigits_nodup n A t hA hd
  have hc : (lowerDigits n A t).count a ≤ 1 := List.nodup_iff_count_le_one.mp hn a
  simpa [targetState, List.count_replicate, ha, Ne.symm ha] using hc

/-- Section 4.4's exclusion of all lower-primary unary factors is obtained
from the digit property, rather than assumed of the target fragments. -/
theorem targetState_no_other_unary (n : Nat) (A : Nat → Nat) (t a d : Nat)
    (hA : Function.Injective A) (hd : ∀ u < t, baseDigit n u ≤ 1)
    (ha : a ≠ A t) (hlen : 2 ≤ d) :
    scanCount (List.replicate d a) (targetState n A t) = 0 := by
  have hv : List.replicate d a ≠ [] := by simp; omega
  have hp := (scanCount_is_maximum (List.replicate d a) (targetState n A t) hv).1
  have hc := hp.symbol_count_bound a
  have ht := targetState_other_count n A t a hA hd ha
  simp only [List.count_replicate_self] at hc
  have hm := Nat.mul_le_mul_left (scanCount (List.replicate d a) (targetState n A t)) hlen
  omega

theorem targetState_mem (n : Nat) (A : Nat → Nat) (t a : Nat)
    (ha : a ∈ targetState n A t) : ∃ u ≤ t, a = A u := by
  rcases List.mem_append.mp ha with ha | ha
  · exact ⟨t, Nat.le_refl _, (List.mem_replicate.mp ha).2⟩
  · obtain ⟨u, hu, he⟩ := lowerDigits_mem n A t a ha
    exact ⟨u, by omega, he⟩

/-- Exhaustive target-factor classification. A repeated active-symbol factor
is unary; every other possible length-at-least-two factor contains two
different primary symbols. -/
theorem targetState_factor_cases (n : Nat) (A : Nat → Nat) (t : Nat)
    (hA : Function.Injective A) (hd : ∀ u < t, baseDigit n u ≤ 1)
    (v : Word Nat) (hv : 2 ≤ v.length)
    (hc : 0 < scanCount v (targetState n A t)) :
    v = List.replicate v.length (A t) ∨
      ∃ a ∈ v, ∃ b ∈ v, a ≠ b ∧ (∃ i ≤ t, a = A i) ∧ (∃ j ≤ t, b = A j) := by
  have hvn : v ≠ [] := by intro he; simp [he] at hv
  have hin := (scanCount_is_maximum v (targetState n A t) hvn).1.factor_isInfix hc
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil v hvn
  by_cases hall : ∀ b ∈ v, b = a
  · have he : v = List.replicate v.length a := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
    by_cases hax : a = A t
    · exact Or.inl (by simpa [hax] using he)
    · have hz := targetState_no_other_unary n A t a v.length hA hd hax hv
      rw [← he] at hz
      omega
  · have hex : ∃ b ∈ v, b ≠ a := by
      by_contra hn
      apply hall
      intro b hb
      by_contra hba
      exact hn ⟨b, hb, hba⟩
    obtain ⟨b, hb, hba⟩ := hex
    exact Or.inr ⟨a, ha, b, hb, Ne.symm hba,
      targetState_mem n A t a (hin.subset ha), targetState_mem n A t b (hin.subset hb)⟩

theorem Scan.unary_with_absent_tail (d n X Y : Nat) (tail : Word Nat)
    (hd : 0 < d) (ht : X ∉ tail) :
    Scan (List.replicate d X) Y (List.replicate n X ++ tail)
      (List.replicate (n/d) Y ++ List.replicate (n%d) X ++ tail) (n/d) := by
  have hv : List.replicate d X ≠ [] := by simp; omega
  cases tail with
  | nil => simpa using Scan.unary_division d n X Y hd
  | cons z tail =>
    have hz : z ≠ X := by intro he; subst z; exact ht (by simp)
    have htail : X ∉ tail := fun hm => ht (by simp [hm])
    have hx : X ∈ List.replicate d X := by simp; omega
    have hc := scanCount_zero_of_missing (List.replicate d X) tail X hx htail
    have hs := scanOutput_spec (List.replicate d X) Y tail hv
    rw [hc, scanOutput_eq_self _ Y tail hv hc] at hs
    simpa only [Nat.add_zero, List.append_assoc] using
      hs.unary_division_before_marker d n X Y z hd hz

/-- Every intended substitution advances the target exactly one base-64
digit. This theorem does not assume a particular target integer. -/
theorem targetState_advance (n : Nat) (A : Nat → Nat) (t : Nat)
    (hA : Function.Injective A) :
    Scan (List.replicate 64 (A t)) (A (t+1)) (targetState n A t)
      (targetState n A (t+1)) (n/64^(t+1)) := by
  have hs := Scan.unary_with_absent_tail 64 (n/64^t) (A t) (A (t+1))
    (lowerDigits n A t) (by decide) (lowerDigits_avoids_active n A t hA)
  have he : n/64^t/64 = n/64^(t+1) := by rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
  simpa only [targetState, lowerDigits, baseDigit, he, List.append_assoc] using hs

theorem targetState_initial (n : Nat) (A : Nat → Nat) :
    targetState n A 0 = List.replicate n (A 0) := by simp [targetState, lowerDigits]

theorem targetState_length_le (n : Nat) (A : Nat → Nat) (t : Nat)
    (hA : Function.Injective A) : (targetState n A t).length ≤ n := by
  induction t with
  | zero => simp [targetState_initial]
  | succ t ih =>
    have hh := (targetState_advance n A t hA).benefit (by simp)
    omega

end GreedyLowerBound
