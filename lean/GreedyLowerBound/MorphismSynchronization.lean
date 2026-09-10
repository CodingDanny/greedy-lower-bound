import GreedyLowerBound.Morphism

set_option autoImplicit false

namespace GreedyLowerBound

theorem muWord_two_blocks (w : Word Letter) (i o : Nat) (hi : i < w.length)
    (ho : o < 19) (hb : 19 * i + o + 7 ≤ 19 * w.length) (b : Letter)
    (hnext : ∀ hn : i + 1 < w.length, b = w[i+1]) :
    ∀ k : Fin 7, (muWord w)[19*i+o+k.val]? =
      (mu w[i] ++ mu b)[o+k.val]? := by
  intro k
  by_cases hk : o + k.val < 19
  · rw [List.getElem?_append_left (by simpa only [mu_length] using hk)]
    simpa only [Nat.add_assoc] using muWord_get w i (o+k.val) hi hk
  · have hn : i + 1 < w.length := by omega
    have hk' : o + k.val - 19 < 19 := by omega
    have he : 19*i+o+k.val = 19*(i+1)+(o+k.val-19) := by omega
    rw [he, muWord_get w (i+1) (o+k.val-19) hn hk',
      List.getElem?_append_right (by rw [mu_length]; omega), mu_length, hnext hn]

/-- The last block needs no actual successor: a different fictitious successor
can be used because all seven queried positions are inside the original word. -/
theorem muWord_window_cover (w : Word Letter) (hg : PowerFree w) (p : Nat)
    (hp : p + 7 ≤ (muWord w).length) :
    ∃ a b : Letter, a ≠ b ∧ ∀ k : Fin 7,
      (muWord w)[p+k.val]? = (mu a ++ mu b)[p%19+k.val]? := by
  rw [muWord_length] at hp
  have hi : p / 19 < w.length := by omega
  have ho : p % 19 < 19 := by omega
  have he : 19 * (p / 19) + p % 19 = p := by omega
  let a := w[p/19]
  by_cases hn : p/19+1 < w.length
  · let b := w[p/19+1]
    have hab : a ≠ b := by
      have hh := hg.no_equal_neighbors (p/19) hn
      simpa [a, b, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hn] using hh
    refine ⟨a, b, hab, ?_⟩
    have ht := muWord_two_blocks w (p/19) (p%19) hi ho (by omega) b (fun _ => rfl)
    simpa only [he] using ht
  · let b : Letter := if a = 0 then 1 else 0
    have hab : a ≠ b := by
      dsimp [b]
      split
      · next ha => simp only [ha]; decide
      · next ha => exact ha
    refine ⟨a, b, hab, ?_⟩
    have ht := muWord_two_blocks w (p/19) (p%19) hi ho (by omega) b
      (fun h => False.elim (hn h))
    simpa only [he] using ht

theorem mu_row_synchronizes (w : Word Letter) (hg : PowerFree w)
    (p : Nat) (hp : p + 7 ≤ (muWord w).length) (c : Letter) (t : Fin 2)
    (he : ∀ k : Fin 7, (muWord w)[p+k.val]? = (mu c)[12*t.val+k.val]?) :
    p % 19 = 12 * t.val := by
  obtain ⟨a, b, hab, hc⟩ := muWord_window_cover w hg p hp
  exact (mu_synchronization_chars a b c hab ⟨p%19, by omega⟩ t
    (fun k => (hc k).symm.trans (he k))).1

theorem choose_mu_row (a N : Nat) (ha : a + 18 ≤ 19 * N) :
    ∃ i : Nat, ∃ t : Fin 2, ∃ δ : Nat,
      δ + 7 ≤ 18 ∧ a + δ = 19 * i + 12 * t.val ∧ i < N := by
  by_cases hz : a % 19 = 0
  · refine ⟨a/19, 0, 0, ?_, ?_, ?_⟩ <;> omega
  · by_cases hm : a % 19 ≤ 12
    · refine ⟨a/19, 1, 12-a%19, ?_, ?_, ?_⟩ <;> omega
    · refine ⟨a/19+1, 0, 19-a%19, ?_, ?_, ?_⟩ <;> omega

/-- Appendix A.1's unbounded conclusion from its finite table. -/
theorem mu_equal_intervals_synchronize (w : Word Letter) (hg : PowerFree w)
    (a b r : Nat) (ha : a+r ≤ (muWord w).length) (hb : b+r ≤ (muWord w).length)
    (hr : 18 ≤ r) (he : EqualIntervals (muWord w) a b r) : a % 19 = b % 19 := by
  have halen : a + 18 ≤ 19 * w.length := by rw [muWord_length] at ha; omega
  obtain ⟨i, t, δ, hd, had, hi⟩ := choose_mu_row a w.length halen
  have hm : (b+δ) % 19 = 12*t.val := by
    apply mu_row_synchronizes w hg (b+δ) (by omega) w[i] t
    intro k
    have hk : δ + k.val < r := by omega
    have hrow := muWord_get w i (12*t.val+k.val) hi (by have ht := t.isLt; omega)
    have heq := he (δ+k.val) hk
    have hidx : a+(δ+k.val) = 19*i+(12*t.val+k.val) := by omega
    rw [hidx] at heq
    simpa only [Nat.add_assoc] using heq.symm.trans hrow
  have ht := t.isLt
  omega

end GreedyLowerBound
