import GreedyLowerBound.OptimalGrammar

set_option autoImplicit false
namespace GreedyLowerBound

theorem inputRest_length (h : Nat) (D : List Bool) :
    (inputRest h D).length = h^2-1+h := by
  simp [inputRest, targetNumbers_length]

theorem inputStart_eq (h : Nat) (D : List Bool) (hh : 1 ≤ h) :
    inputStart h D = h^2+4*h := by
  have hp : 1 ≤ h^2 := Nat.one_le_pow _ _ hh
  rw [inputStart, inputRest_length]
  omega

/-- Every alphabet name below the start symbol occurs in the constructed
word: a, all 3h private markers, and all h²+h-1 separators. -/
theorem inputWord_alphabet (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) :
    (inputWord h D).toFinset = Finset.range (h^2+4*h) := by
  apply Finset.ext
  intro a
  rw [List.mem_toFinset, Finset.mem_range]
  constructor
  · intro ha
    have hb := numbered_join_bound (inputFirst h D) (inputRest h D) (1+3*h)
      (inputFirst_bound h D) (inputRest_bound h D) a ha
    change a < inputStart h D at hb
    rwa [inputStart_eq h D hh] at hb
  · intro ha
    by_cases hz : a = 0
    · subst a
      exact inputWord_contains_zero h D hh hD
    · by_cases hm : a < 1+3*h
      · let j := (a-1)/3
        let c : Letter := ⟨(a-1)%3, Nat.mod_lt _ (by decide)⟩
        have hj : j < h := by dsimp [j]; omega
        have he : markerName j c = a := by dsimp [markerName, j, c]; omega
        rw [← he]
        exact inputWord_contains_marker h D j hj c
      · have hk : a-(1+3*h) < (inputRest h D).length := by
          rw [← inputStart_eq h D hh] at ha
          unfold inputStart at ha
          omega
        have hc := numbered_join_separator (inputFirst h D) (inputRest h D)
          (1+3*h) (a-(1+3*h)) hk (inputFirst_bound h D) (inputRest_bound h D)
        have he : 1+3*h+(a-(1+3*h)) = a := by omega
        rw [he] at hc
        apply List.count_pos_iff.mp
        change 0 < (joinFragments (inputFirst h D) (numberedRest (1+3*h) (inputRest h D))).count a
        omega

theorem inputWord_alphabet_card (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) : (inputWord h D).toFinset.card = h^2+4*h := by
  rw [inputWord_alphabet h D hh hD, Finset.card_range]

theorem input_minimumSize_lower (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) : h^2+4*h ≤ Grammar.minimumSize (inputWord h D) := by
  rw [← inputWord_alphabet_card h D hh hD]
  exact Grammar.alphabet_card_le_minimumSize _ (inputWord_nonempty h D hh hD)

end GreedyLowerBound
