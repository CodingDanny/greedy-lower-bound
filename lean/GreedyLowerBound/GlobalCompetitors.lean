import GreedyLowerBound.ActiveStorage

set_option autoImplicit false

namespace GreedyLowerBound

theorem Grammar.gain_mono_frequency (G : Grammar) (v : Word Nat) (c : Nat)
    (hv : 1 ≤ v.length) (hc : c ≤ G.frequency v) :
    replacementGain c v.length ≤ G.gain v := by
  have hc' := Int.ofNat_le.mpr hc
  have hl : (0 : Int) ≤ (v.length : Int)-1 := by omega
  have hm := mul_le_mul_of_nonneg_right hc' hl
  exact sub_le_sub_right hm v.length

/-- A private marker's unique cell owner gives the exact *global* count used
in Lemma 2. This includes every additional right-hand side. -/
theorem Fragmentation.marker_frequency {G : Grammar} (P : Fragmentation G)
    (left right : List (Word Nat)) (owner v : Word Nat) (a : Nat)
    (hpieces : P.pieces.Perm (left ++ owner :: right)) (hv : G.Eligible v)
    (ha : a ∈ v) (hl : ∀ w ∈ left, a ∉ w) (hr : ∀ w ∈ right, a ∉ w) :
    G.frequency v = scanCount v owner := by
  rw [P.frequency_eq v hv, (hpieces.map (scanCount v)).sum_eq]
  exact cellFrequency_confined left right owner v a ha hl hr

/-- Section 4.3 with the local-to-global step discharged: no eligible factor
containing a private marker can compete with the intended unary factor. -/
theorem Fragmentation.auxiliary_marker_loses {G : Grammar} (P : Fragmentation G)
    (h j k : Nat) (hh : 1 ≤ h) (hj : j ≤ h) (hk : 1 ≤ k)
    (f : Option Letter → Nat) (hf : Function.Injective f)
    (left right : List (Word Nat))
    (hpieces : P.pieces.Perm (left ++
      [(auxiliaryWord (64*k) (muIterate (auxiliaryExponent h j))).map f] ++ right))
    (v : Word Nat) (hv : G.Eligible v) (a : Nat) (ha : a ∈ v) (hax : a ≠ f none)
    (hl : ∀ w ∈ left, a ∉ w) (hr : ∀ w ∈ right, a ∉ w) :
    G.gain v < G.gain (List.replicate 64 (f none)) := by
  let owner := (auxiliaryWord (64*k) (muIterate (auxiliaryExponent h j))).map f
  have hvn : v ≠ [] := by intro he; have hh := hv.1; simp [he] at hh
  have hfreq := P.marker_frequency left right owner v a
    (by simpa only [List.append_assoc, List.singleton_append] using hpieces) hv ha hl hr
  have hc : 2 ≤ scanCount v owner := by rw [← hfreq]; exact hv.2
  have hp := (scanCount_is_maximum v owner hvn).1
  have hlocal := GreedyLowerBound.auxiliary_marker_loses h j k hh hj hk f hf
    v (scanCount v owner) hp hc ⟨a, ha, hax⟩
  have hmem : owner ∈ P.pieces := hpieces.mem_iff.mpr (by simp [owner])
  have hB := P.scanCount_le_frequency (List.replicate 64 (f none)) owner (by simp) hmem
  have hz : ∀ z ∈ (muIterate (auxiliaryExponent h j)).map (fun a => f (some a)),
      z ≠ f none := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
    intro he
    exact Option.noConfusion (hf he)
  rw [show owner = paddedRuns (f none) (64*k)
      ((muIterate (auxiliaryExponent h j)).map (fun a => f (some a))) from
        auxiliaryWord_renamed _ _ _,
    scanCount_paddedRuns (f none) 64 (64*k) _ (by decide) hz,
    List.length_map, muIterate_length] at hB
  have hdiv : 64*k/64 = k := by omega
  rw [hdiv] at hB
  have hgain := G.gain_mono_frequency (List.replicate 64 (f none))
    (auxiliaryLength h j*k) (by simp) hB
  simp only [List.length_replicate] at hgain
  have heq : G.gain v = replacementGain (scanCount v owner) v.length := by
    unfold Grammar.gain replacementGain
    rw [hfreq]
  rw [heq]
  exact hlocal.trans_le hgain

/-- Section 4.4's quantitative conclusion, once ownership has confined the
factor to target cells. -/
theorem ActiveStorage.target_factor_loses {G : Grammar} {X : Nat}
    (S : ActiveStorage G X) (H : Nat) (hH : cellMass S.targets ≤ H)
    (hM : H+64 < S.current.length) (v : Word Nat)
    (hf : G.frequency v = cellFrequency S.targets v) :
    G.gain v < G.gain (List.replicate 64 X) := by
  have hv := S.benchmark_eligible (by omega)
  have hc := S.current_le_frequency hv
  have hg := G.gain_mono_frequency (List.replicate 64 X) S.current.length (by simp) hc
  have ht := G.gain_le_mass_of_frequency v S.targets hf
  simp only [List.length_replicate, replacementGain] at hg
  have hH' : (cellMass S.targets : Int) ≤ H := by omega
  have hM' : (H : Int)+64 < S.current.length := by omega
  omega

end GreedyLowerBound
