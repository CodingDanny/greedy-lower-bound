import GreedyLowerBound.InputAlphabet

set_option autoImplicit false
namespace GreedyLowerBound

theorem numbered_join_length (first : Word Nat) (rest : List (Word Nat)) (base : Nat) :
    (joinFragments first (numberedRest base rest)).length =
      first.length + (rest.map List.length).sum + rest.length := by
  induction rest generalizing first base with
  | nil => simp [joinFragments, numberedRest]
  | cons w rest ih =>
    change (first ++ base :: joinFragments w (numberedRest (base+1) rest)).length = _
    rw [List.length_append, List.length_cons, ih]
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- Exact input-length accounting, including every separator. -/
theorem inputWord_length (h : Nat) (D : List Bool) :
    (inputWord h D).length = (targetNumbers h D).sum +
      ((List.range h).map (fun j => auxiliaryLength h (j+1)*(64^(j+1)+1))).sum +
      (h^2-1+h) := by
  rw [inputWord, numbered_join_length]
  have hs : (inputFirst h D).length +
      (((targetNumbers h D).tail.map (fun n => List.replicate n 0)).map List.length).sum =
      (targetNumbers h D).sum := by
    simp only [inputFirst, List.length_replicate, List.map_map]
    generalize targetNumbers h D = ns
    cases ns <;> simp [Function.comp_def]
  rw [inputRest_length]
  change (inputFirst h D).length +
    ((inputRest h D).map List.length).sum + (h^2-1+h) = _
  simp only [inputRest, List.map_append, List.sum_append]
  have haux : (((List.range h).map (inputAuxiliary h)).map List.length).sum =
      ((List.range h).map (fun j => auxiliaryLength h (j+1)*(64^(j+1)+1))).sum := by
    apply congrArg List.sum
    rw [List.map_map]
    exact List.map_congr_left (fun j _ => inputAuxiliary_length h j)
  rw [haux]
  omega

/-- Each auxiliary contributes at most twice 19^(7h) * 64^h. -/
theorem inputAuxiliary_length_upper (h j : Nat) (hj : j < h) :
    (inputAuxiliary h j).length ≤ 2*19^(7*h)*64^h := by
  have he : auxiliaryExponent h (j+1) ≤ 7*h := by unfold auxiliaryExponent; omega
  have hM : auxiliaryLength h (j+1) ≤ 19^(7*h) := Nat.pow_le_pow_right (by decide) he
  have hB : 64^(j+1) ≤ 64^h := Nat.pow_le_pow_right (by decide) (by omega)
  have hp : 1 ≤ 64^h := Nat.one_le_pow _ _ (by decide)
  rw [inputAuxiliary_length]
  calc
    _ ≤ 19^(7*h)*(2*64^h) := Nat.mul_le_mul hM (by omega)
    _ = _ := by ac_rfl

theorem inputAuxiliary_total_upper (h : Nat) :
    ((List.range h).map (fun j => auxiliaryLength h (j+1)*(64^(j+1)+1))).sum ≤ 2^(42*h+1) := by
  have hh : h ≤ 2^h := Nat.le_of_lt Nat.lt_two_pow_self
  have hM : 19^(7*h) ≤ 32^(7*h) := Nat.pow_le_pow_left (by decide) _
  have hsum : ((List.range h).map (fun j => auxiliaryLength h (j+1)*(64^(j+1)+1))).sum ≤
      h*(2*19^(7*h)*64^h) := by
    calc
      _ ≤ ((List.range h).map (fun _ => 2*19^(7*h)*64^h)).sum := by
        apply List.sum_le_sum
        intro j hj
        have hb := inputAuxiliary_length_upper h j (List.mem_range.mp hj)
        rwa [inputAuxiliary_length] at hb
      _ = _ := by simp [List.map_const']
  calc
    _ ≤ h*(2*19^(7*h)*64^h) := hsum
    _ ≤ 2^h*(2*(2^5)^(7*h)*(2^6)^h) :=
      Nat.mul_le_mul hh (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hM))
    _ = 2^(42*h+1) := by
      rw [← Nat.pow_mul, ← Nat.pow_mul]
      change 2^h*(2^1*2^(5*(7*h))*2^(6*h)) = _
      rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
      congr 1
      omega

/-- Exponential upper bound on the full input, without dropping separators. -/
theorem inputWord_length_upper (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) : (inputWord h D).length ≤ 2^(50*h) := by
  have ht := (targetNumbers_sum_le h D hD).trans (targetMass_le_two_pow h)
  have ha := inputAuxiliary_total_upper h
  have hp : h ≤ 2^h := Nat.le_of_lt Nat.lt_two_pow_self
  have hs : h^2-1+h ≤ 2^(2*h+1) := by
    have hh2 : h ≤ h^2 := by nlinarith
    have hb := Nat.pow_le_pow_left hp 2
    have he : (2^h)^2 = 2^(2*h) := by rw [← Nat.pow_mul]; congr 1; omega
    rw [he] at hb
    rw [Nat.pow_succ 2 (2*h)]
    omega
  have ht' : 2^(14*h) ≤ 2^(42*h+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hs' : 2^(2*h+1) ≤ 2^(42*h+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hb : (inputWord h D).length ≤ 3*2^(42*h+1) := by rw [inputWord_length]; omega
  calc
    _ ≤ 3*2^(42*h+1) := hb
    _ ≤ 2^(42*h+3) := by
      have he : 42*h+3 = (42*h+1)+2 := by omega
      rw [he, Nat.pow_add 2 (42*h+1) 2]
      change 3*2^(42*h+1) ≤ 2^(42*h+1)*4
      omega
    _ ≤ 2^(50*h) := Nat.pow_le_pow_right (by decide) (by omega)

/-- A single last auxiliary already gives exponential growth. -/
theorem inputWord_length_lower (h : Nat) (D : List Bool) (hh : 1 ≤ h) :
    2^h ≤ (inputWord h D).length := by
  let weights := (List.range h).map (fun j => auxiliaryLength h (j+1)*(64^(j+1)+1))
  have hm : auxiliaryLength h h*(64^h+1) ∈ weights := by
    apply List.mem_map.mpr
    refine ⟨h-1, List.mem_range.mpr (by omega), ?_⟩
    have he : h-1+1 = h := by omega
    rw [he]
  have hs := List.le_sum_of_mem hm
  have hM : 2^h ≤ auxiliaryLength h h := by
    unfold auxiliaryLength
    rw [auxiliaryExponent_last]
    exact (Nat.pow_le_pow_left (by decide : 2 ≤ 19) h).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hm' : auxiliaryLength h h ≤ auxiliaryLength h h*(64^h+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  rw [inputWord_length]
  dsimp [weights] at hs
  omega

end GreedyLowerBound
