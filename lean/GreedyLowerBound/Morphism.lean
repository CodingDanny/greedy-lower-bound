import GreedyLowerBound.MorphismFinite

set_option autoImplicit false

namespace GreedyLowerBound

/-- Random access into a uniform morphism, including its precise block offset. -/
theorem muWord_get (w : Word Letter) (i o : Nat) (hi : i < w.length) (ho : o < 19) :
    (muWord w)[19 * i + o]? = (mu w[i])[o]? := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a w ih =>
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero, muWord,
        List.flatMap_cons]
      exact List.getElem?_append_left (by simpa only [mu_length] using ho)
    | succ i =>
      have hi' : i < w.length := by simpa using hi
      simp only [muWord, List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by rw [mu_length]; omega), mu_length]
      have he : 19 * (i + 1) + o - 19 = 19 * i + o := by omega
      rw [he]
      exact ih i hi'

theorem muWord_get_first (w : Word Letter) (i : Nat) (hi : i < w.length) :
    (muWord w)[19 * i]? = w[i]? := by
  simpa only [Nat.add_zero, List.getElem?_eq_getElem hi] using
    (muWord_get w i 0 hi (by decide)).trans (mu_endpoints w[i]).1

theorem muWord_get_last (w : Word Letter) (i : Nat) (hi : i < w.length) :
    (muWord w)[19 * i + 18]? = w[i]? := by
  simpa only [List.getElem?_eq_getElem hi] using
    (muWord_get w i 18 hi (by decide)).trans (mu_endpoints w[i]).2

theorem muWord_take (w : Word Letter) (k : Nat) (hk : k ≤ w.length) :
    muWord (w.take k) = (muWord w).take (19 * k) := by
  have he : muWord w = muWord (w.take k) ++ muWord (w.drop k) := by
    simp only [muWord, ← List.flatMap_append, List.take_append_drop]
  have hl : (muWord (w.take k)).length = 19 * k := by
    rw [muWord_length, List.length_take, Nat.min_eq_left hk]
  rw [he, List.take_left' hl]

theorem muWord_drop (w : Word Letter) (k : Nat) (hk : k ≤ w.length) :
    muWord (w.drop k) = (muWord w).drop (19 * k) := by
  have he : muWord w = muWord (w.take k) ++ muWord (w.drop k) := by
    simp only [muWord, ← List.flatMap_append, List.take_append_drop]
  have hl : (muWord (w.take k)).length = 19 * k := by
    rw [muWord_length, List.length_take, Nat.min_eq_left hk]
  rw [he, List.drop_left' hl]

theorem mu_synchronization_chars (a b c : Letter) (hab : a ≠ b)
    (i : Fin 19) (t : Fin 2)
    (he : ∀ k : Fin 7, (mu a ++ mu b)[i.val + k.val]? =
      (mu c)[12 * t.val + k.val]?) : i.val = 12 * t.val ∧ a = c := by
  apply mu_synchronization_table a b c hab i t
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 7
  · simpa only [List.getElem?_take, hk, ↓reduceIte, List.getElem?_drop] using he ⟨k, hk⟩
  · simp only [List.getElem?_take, hk, ↓reduceIte]

end GreedyLowerBound
