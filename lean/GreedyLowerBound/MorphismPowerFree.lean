import GreedyLowerBound.MorphismSynchronization

set_option autoImplicit false

namespace GreedyLowerBound

/-- The minimal-counterexample argument of Appendix A.3, expressed as strong
induction. Both partially covered end blocks are handled explicitly. -/
theorem mu_preserves_powerFree_by_length (n : Nat) :
    ∀ w : Word Letter, w.length = n → PowerFree w → PowerFree (muWord w) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro w hn hg
    by_cases hshort : n ≤ 3
    · exact mu_short_powerFree w hg (by omega)
    have hn4 : 4 ≤ n := by omega
    intro a L p hb hp hper
    by_cases hgood : 4 * L ≤ 7 * p
    · exact hgood
    have hlen : (muWord w).length = 19 * n := by rw [muWord_length, hn]
    have hpL : p < L := by omega
    by_cases ha : 19 ≤ a
    · have hwd : (w.drop 1).length = n - 1 := by simp only [List.length_drop, hn]
      have hdg := ih (n-1) (by omega) (w.drop 1) hwd (hg.drop 1)
      apply hdg (a-19) L p
      · rw [muWord_length, hwd]; omega
      · exact hp
      · intro k hk
        rw [muWord_drop w 1 (by omega), List.getElem?_drop, List.getElem?_drop]
        have he1 : 19*1+(a-19+k) = a+k := by omega
        have he2 : 19*1+(a-19+k+p) = a+k+p := by omega
        rw [he1, he2]
        exact hper k hk
    have ha18 : a ≤ 18 := by omega
    by_cases hend : a + L ≤ 19 * (n-1)
    · have hwt : (w.take (n-1)).length = n-1 := by
        rw [List.length_take, hn, Nat.min_eq_left (by omega)]
      have htg := ih (n-1) (by omega) (w.take (n-1)) hwt (hg.take (n-1))
      apply htg a L p
      · rw [muWord_length, hwt]; exact hend
      · exact hp
      · intro k hk
        rw [muWord_take w (n-1) (by omega),
          List.getElem?_take_of_lt (by omega : a+k < 19*(n-1)),
          List.getElem?_take_of_lt (by omega : a+k+p < 19*(n-1))]
        exact hper k hk
    have hL40 : 40 ≤ L := by omega
    have hr18 : 18 ≤ L-p := by omega
    have heq : EqualIntervals (muWord w) a (a+p) (L-p) := by
      intro k hk
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hper k (by omega : k+p < L)
    have hsync := mu_equal_intervals_synchronize w hg a (a+p) (L-p)
      (by omega) (by omega) hr18 heq
    have hp19 : p = 19 * (p/19) := by omega
    let d := p/19
    have hd : 0 < d := by dsimp [d]; omega
    have hpd : p = 19 * d := hp19
    have hdn : d ≤ n-2 := by omega
    have hbadn : 7*d < 4*n := by omega
    have hwp : PeriodAt w 0 n d := by
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        have hfirst := hper (18-a) (by omega : 18-a+p < L)
        have he1 : a+(18-a) = 19*0+18 := by omega
        have he2 : a+(18-a)+p = 19*d+18 := by omega
        rw [he2, he1, muWord_get_last w 0 (by omega),
          muWord_get_last w d (by omega)] at hfirst
        simpa only [Nat.zero_add] using hfirst
      · have hi := hper (19*k-a) (by omega : 19*k-a+p < L)
        have he1 : a+(19*k-a) = 19*k := by omega
        have he2 : a+(19*k-a)+p = 19*(k+d) := by omega
        rw [he2, he1, muWord_get_first w k (by omega),
          muWord_get_first w (k+d) (by omega)] at hi
        simpa only [Nat.zero_add] using hi
    have hcontra := hg 0 n d (by omega) hd hwp
    omega

theorem mu_preserves_powerFree (w : Word Letter) (hg : PowerFree w) :
    PowerFree (muWord w) := mu_preserves_powerFree_by_length w.length w rfl hg

def muIterate : Nat → Word Letter
  | 0 => [0]
  | e+1 => muWord (muIterate e)

/-- The full finite-iterate property used in Lemma 1, with no appeal to an
external theorem about Dejean's morphism. -/
theorem muIterate_powerFree (e : Nat) : PowerFree (muIterate e) := by
  induction e with
  | zero => exact PowerFree.of_length_le_one [0] (by decide)
  | succ e ih => exact mu_preserves_powerFree (muIterate e) ih

theorem muIterate_length (e : Nat) : (muIterate e).length = 19^e := by
  induction e with
  | zero => rfl
  | succ e ih =>
    simp only [muIterate, muWord_length, ih, Nat.pow_succ, Nat.mul_comm]

theorem muIterate_spacing (e a d r : Nat)
    (hb : a+d+r ≤ 19^e) (hd : 0 < d)
    (he : EqualIntervals (muIterate e) a (a+d) r) : 4*r ≤ 3*d := by
  exact occurrence_spacing (muIterate e) (muIterate_powerFree e) a d r
    (by simpa only [muIterate_length] using hb) hd he

end GreedyLowerBound
