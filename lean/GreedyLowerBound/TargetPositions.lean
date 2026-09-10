import GreedyLowerBound.IndexReconstruction
import GreedyLowerBound.TargetDensity
import Mathlib.Data.Finset.Max

set_option autoImplicit false
namespace GreedyLowerBound

/-- Any nonempty list of distinct indices spans at least its own length. -/
theorem nodup_index_span (v : List Nat) (hv : v ≠ []) (hd : v.Nodup) :
    ∃ lo ∈ v, ∃ hi ∈ v, lo ≤ hi ∧ v.length ≤ hi+1-lo := by
  have hn : v.toFinset.Nonempty := by
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil v hv
    exact ⟨a, List.mem_toFinset.mpr ha⟩
  let lo := v.toFinset.min' hn
  let hi := v.toFinset.max' hn
  have hlo : lo ∈ v := List.mem_toFinset.mp (Finset.min'_mem _ hn)
  have hhi : hi ∈ v := List.mem_toFinset.mp (Finset.max'_mem _ hn)
  have hlow : ∀ a ∈ v, lo ≤ a := fun a ha => Finset.min'_le _ _ (List.mem_toFinset.mpr ha)
  have hhigh : ∀ a ∈ v, a ≤ hi := fun a ha => Finset.le_max' _ _ (List.mem_toFinset.mpr ha)
  refine ⟨lo, hlo, hi, hhi, hlow hi hhi, ?_⟩
  have hsub : v.toFinset ⊆ (Finset.range (hi+1-lo)).image (fun a => a+lo) := by
    intro a ha
    have hl := hlow a (List.mem_toFinset.mp ha)
    have hh := hhigh a (List.mem_toFinset.mp ha)
    exact Finset.mem_image.mpr ⟨a-lo, Finset.mem_range.mpr (by omega), by omega⟩
  have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
  simpa only [List.toFinset_card_of_nodup hd, Finset.card_range] using hc

def targetWindow (h : Nat) (D : List Bool) (s i : Nat) : List Bool :=
  slice (chunk h D s) (i+1) h

def targetIndexWord (h : Nat) (D : List Bool) (s i : Nat) : List Nat :=
  oneIndices (targetWindow h D s i)

theorem targetWindow_length (h : Nat) (D : List Bool) (s i : Nat)
    (hD : D.length = h^2) (hs : s < h) (hi : i < h) :
    (targetWindow h D s i).length = h := by
  apply slice_length
  rw [chunk_length h D s hD hs]
  omega

theorem targetIndexWord_nodup (h : Nat) (D : List Bool) (s i : Nat) :
    (targetIndexWord h D s i).Nodup :=
  (oneIndices_pairwise _).imp (fun hab => Nat.ne_of_gt hab)

theorem targetIndexWord_length_lower (h : Nat) (D : List Bool) (s i : Nat)
    (hD : D.length = h^2) (hs : s < h) (hi : i < h) :
    h/2-1 ≤ (targetIndexWord h D s i).length := by
  have hb := target_lowerDigits_length h D s i hD hs hi id
  rw [target_lowerDigits_window h D s i hD hs hi id, List.map_id] at hb
  exact hb

theorem targetWindow_get (h : Nat) (D : List Bool) (s i k : Nat) (hi : i < h) (hk : k < h) :
    (targetWindow h D s i)[k]? = (binaryEncode D)[2*h*s+(i+1+k)]? := by
  rw [targetWindow, slice_get _ _ _ _ hk, chunk_eq_slice,
    slice_get _ _ _ _ (by omega)]

/-- Global start of the bit selected by primary index j in target (s,i). -/
def targetBitStart (h s i j : Nat) : Nat := 2*h*s+(h+i-j)

theorem targetBitStart_chunk (h s i j : Nat) (hh : 0 < h) (hi : i < h) (hj : j < h) :
    targetBitStart h s i j / (2*h) = s := by
  unfold targetBitStart
  have ho : h+i-j < 2*h := by omega
  rw [Nat.mul_add_div (by omega : 0 < 2*h), Nat.div_eq_of_lt ho, Nat.add_zero]

theorem targetBitStart_injective (h s i s' i' j : Nat) (hh : 0 < h)
    (hi : i < h) (hi' : i' < h) (hj : j < h)
    (he : targetBitStart h s i j = targetBitStart h s' i' j) : s = s' ∧ i = i' := by
  have hs : s = s' := by
    rw [← targetBitStart_chunk h s i j hh hi hj, ← targetBitStart_chunk h s' i' j hh hi' hj, he]
  subst s'
  unfold targetBitStart at he
  exact ⟨rfl, by omega⟩

/-- Literal target-factor reconstruction transported to the single encoded
seed. The interval length and all endpoint bounds are explicit. -/
theorem target_factor_reconstruct (h : Nat) (D : List Bool) (s i s' i' : Nat)
    (hD : D.length = h^2) (hs : s < h) (hi : i < h) (hs' : s' < h) (hi' : i' < h)
    (v : List Nat) (hv : v.IsInfix (targetIndexWord h D s i))
    (hv' : v.IsInfix (targetIndexWord h D s' i')) (lo top : Nat)
    (hlo : lo ∈ v) (htop : top ∈ v) (hlt : lo ≤ top) :
    EqualIntervals (binaryEncode D) (targetBitStart h s i top)
      (targetBitStart h s' i' top) (top+1-lo) := by
  have hw := targetWindow_length h D s i hD hs hi
  have hw' := targetWindow_length h D s' i' hD hs' hi'
  have hj := oneIndices_mem_lt (targetWindow h D s i) top (hv.subset htop)
  rw [hw] at hj
  have he := equal_index_factors_reconstruct (targetWindow h D s i)
    (targetWindow h D s' i') v hv hv' lo top hlo htop hlt
  rw [hw, hw'] at he
  intro k hk
  have hp : h-1-top+k < h := by omega
  have heq := he k hk
  rw [targetWindow_get _ _ _ _ _ hi hp, targetWindow_get _ _ _ _ _ hi' hp] at heq
  have hea : 2*h*s+(i+1+(h-1-top+k)) = targetBitStart h s i top+k := by
    unfold targetBitStart
    omega
  have heb : 2*h*s'+(i'+1+(h-1-top+k)) = targetBitStart h s' i' top+k := by
    unfold targetBitStart
    omega
  rwa [hea, heb] at heq

theorem targetBitStart_span_bound (h : Nat) (D : List Bool) (s i lo top : Nat)
    (hD : D.length = h^2) (hs : s < h) (hi : i < h) (htop : top < h) (hlt : lo ≤ top) :
    targetBitStart h s i top + (top+1-lo) ≤ (binaryEncode D).length := by
  have hm := Nat.mul_le_mul_left (2*h) (show s+1 ≤ h by omega)
  rw [Nat.mul_add, Nat.mul_one] at hm
  rw [binaryEncode_length, hD, Nat.pow_two]
  have he : 2*(h*h) = 2*h*h := by ac_rfl
  rw [he]
  unfold targetBitStart
  omega

/-- A nonempty factor in a distinct-index word has only one starting position. -/
theorem nodup_slice_start_unique (w : List Nat) (hw : w.Nodup) (p q L : Nat)
    (hL : 0 < L) (hp : p+L ≤ w.length) (hq : q+L ≤ w.length)
    (he : slice w p L = slice w q L) : p = q := by
  have he0 := congrArg (fun v : List Nat => v[0]?) he
  change (slice w p L)[0]? = (slice w q L)[0]? at he0
  rw [slice_get _ _ _ _ hL, slice_get _ _ _ _ hL, Nat.add_zero, Nat.add_zero] at he0
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), Option.some.injEq] at he0
  exact hw.getElem_inj_iff.mp he0

end GreedyLowerBound
