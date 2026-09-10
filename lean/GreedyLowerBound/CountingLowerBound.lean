import GreedyLowerBound.TargetOccurrences
import GreedyLowerBound.FrozenTargets

set_option autoImplicit false
namespace GreedyLowerBound

def targetDistinctFactors (h : Nat) (D : List Bool) (L : Nat) : Finset (List Nat) :=
  (targetOccurrences h D L).image (targetOccurrenceFactor h D L)

/-- There are h² interiors, each contributing at least floor(h/4) factor
starts when L <= h/4. This counts occurrences, before identifying equal factors. -/
theorem targetOccurrences_card_lower (h : Nat) (D : List Bool) (L : Nat)
    (hD : D.length = h^2) (hL : 4*L ≤ h) :
    h^2*(h/4) ≤ (targetOccurrences h D L).card := by
  unfold targetOccurrences
  rw [Finset.card_sigma]
  have he : h^2*(h/4) = ∑ _si ∈ (Finset.range h).product (Finset.range h), h/4 := by
    simp [Finset.card_product, Nat.pow_two]
  rw [he]
  apply Finset.sum_le_sum
  intro si hsi
  obtain ⟨hs, hi⟩ := Finset.mem_product.mp hsi
  have hs := Finset.mem_range.mp hs
  have hi := Finset.mem_range.mp hi
  have hb := targetIndexWord_length_lower h D si.1 si.2 hD hs hi
  rw [Finset.card_range]
  omega

/-- The manuscript's h³/8 distinct-factor lower bound, with denominators
cleared. Seed uniqueness and the parameter inequalities are explicit premises. -/
theorem targetDistinctFactors_lower (h : Nat) (D : List Bool) (q L : Nat)
    (hh : 0 < h) (hD : D.length = h^2) (hU : UniqueWindows D q)
    (hq : 2*q+2 ≤ L) (hL : 4*L ≤ h) (h4 : h%4 = 0) :
    h^3 ≤ 8*(targetDistinctFactors h D L).card := by
  have hl := targetOccurrences_card_lower h D L hD hL
  have hu := targetOccurrences_card_le_twice_distinct h D q L hh hD hU hq
  change (targetOccurrences h D L).card ≤ 2*(targetDistinctFactors h D L).card at hu
  have he : h = 4*(h/4) := by omega
  have he' : h^3 = 4*(h^2*(h/4)) := by
    calc
      h^3 = h^2*h := by rw [show 3 = 2+1 from rfl, Nat.pow_succ]
      _ = h^2*(4*(h/4)) := congrArg (fun n => h^2*n) he
      _ = _ := by ac_rfl
  rw [he']
  omega

theorem mem_distinctFactors_of_infix (v w : Word Nat) (hv : v.IsInfix w) :
    v ∈ distinctFactors w v.length := by
  obtain ⟨pre, post, rfl⟩ := hv
  apply Finset.mem_image.mpr
  refine ⟨pre.length, Finset.mem_range.mpr ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · simp [slice, List.drop_append, List.take_append]

/-- Injective primary renaming preserves distinctness. Every index factor
counted above is a real factor of any word containing the hard target blocks. -/
theorem targetDistinctFactors_le_capacity (h : Nat) (D : List Bool) (L : Nat)
    (hD : D.length = h^2) (A : Nat → Nat) (hA : Function.Injective A) (w : Word Nat)
    (hw : ∀ n ∈ targetNumbers h D, (lowerDigits n A h).IsInfix w) :
    (targetDistinctFactors h D L).card ≤ (distinctFactors w L).card := by
  let T := targetDistinctFactors h D L
  have hinj : Function.Injective (List.map A) := List.map_injective_iff.mpr hA
  have hsub : T.image (List.map A) ⊆ distinctFactors w L := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hu
    have hm := (mem_targetOccurrences h D L o).mp ho
    have hn : targetNumber h D o.1.1 o.1.2 ∈ targetNumbers h D :=
      List.mem_flatMap.mpr ⟨o.1.1, List.mem_range.mpr hm.1,
        List.mem_map.mpr ⟨o.1.2, List.mem_range.mpr hm.2.1, rfl⟩⟩
    have hblock := hw (targetNumber h D o.1.1 o.1.2) hn
    rw [target_lowerDigits_window h D o.1.1 o.1.2 hD hm.1 hm.2.1 A] at hblock
    have hfac := ((targetOccurrenceFactor_infix h D L o).map A).trans hblock
    have hvlen : ((targetOccurrenceFactor h D L o).map A).length = L := by
      rw [List.length_map, targetOccurrenceFactor_length h D L o ho]
    have he := mem_distinctFactors_of_infix _ w hfac
    rwa [hvlen] at he
  calc
    _ = (T.image (List.map A)).card := (Finset.card_image_of_injective T hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Numeric lower bound for the actual final Greedy grammar. Unlike the
all-phases theorem alone, this includes the full target-interior count. -/
theorem input_greedy_size_lower (h : Nat) (D : List Bool) (q L : Nat)
    (hh : 0 < h) (hD : D.length = h^2) (hU : UniqueWindows D q)
    (hq : 2*q+2 ≤ L) (hL : 4*L ≤ h) (h4 : h%4 = 0)
    (H : Grammar) (steps : Nat) (run : GreedyRun (inputGrammar h D) H steps)
    (hterm : H.Terminal) : h^3 ≤ 8*(H.size*(L-1)) := by
  obtain ⟨A, hA, w, hw, hc⟩ := input_factor_capacity h D hh hD H steps run hterm
  have hlow := targetDistinctFactors_lower h D q L hh hD hU hq hL h4
  have hmid := targetDistinctFactors_le_capacity h D L hD A hA w hw
  have hu := hc L (by omega)
  exact hlow.trans (Nat.mul_le_mul_left 8 (hmid.trans hu))

/-- Specialization to h=2^r, q=2r and L=4r+2. The de Bruijn seed-existence
obligation remains separate; no existence premise is hidden in the definition. -/
theorem input_greedy_size_lower_power (r : Nat) (hr : 10 ≤ r) (D : List Bool)
    (hD : D.length = (2^r)^2) (hU : UniqueWindows D (2*r))
    (H : Grammar) (steps : Nat) (run : GreedyRun (inputGrammar (2^r) D) H steps)
    (hterm : H.Terminal) : (2^r)^3 ≤ 8*(H.size*(4*r+1)) := by
  have h4 : 2^r%4 = 0 := by
    have he : r = (r-2)+2 := by omega
    rw [he, Nat.pow_add]
    norm_num
  have hh : 0 < 2^r := Nat.pow_pos (by decide)
  have hb := input_greedy_size_lower (2^r) D (2*r) (4*r+2) hh hD hU
    (by omega) (factorLength_le_quarter r hr) h4 H steps run hterm
  have he : 4*r+2-1 = 4*r+1 := by omega
  rwa [he] at hb

end GreedyLowerBound
