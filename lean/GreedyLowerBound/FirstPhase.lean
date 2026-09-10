import GreedyLowerBound.InitialActiveStorage

set_option autoImplicit false

namespace GreedyLowerBound

theorem markerName_pos (j : Nat) (c : Letter) : 0 < markerName j c := by
  unfold markerName
  omega

theorem marker_absent_other_auxiliary (h j k : Nat) (c : Letter) (hjk : j ≠ k) :
    markerName j c ∉ inputAuxiliary h k := by
  intro hm
  rcases inputAuxiliary_mem h k (markerName j c) hm with he | ⟨b, he⟩
  · have hp := markerName_pos j c
    omega
  · exact hjk (markerName_injective he).1

theorem input_nonzero_factor_marker (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (v : Word Nat) (hv : (inputGrammar h D).Eligible v) (a : Nat) (ha : a ∈ v)
    (ha0 : a ≠ 0) : ∃ j < h, ∃ c : Letter, a = markerName j c := by
  obtain ⟨w, hw, hc⟩ := (inputPartition h D).eligible_occurs_piece v hv
  have hvn : v ≠ [] := by intro he; have hh := hv.1; simp [he] at hh
  have hin := (scanCount_is_maximum v w hvn).1.factor_isInfix hc
  have ham := hin.subset ha
  rw [inputPartition_pieces h D hh] at hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hw
    exact False.elim (ha0 (List.mem_replicate.mp ham).2)
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
    rcases inputAuxiliary_mem h j a ham with he | ⟨c, he⟩
    · exact False.elim (ha0 he)
    · exact ⟨j, List.mem_range.mp hj, c, he⟩

theorem input_marker_factor_loses (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (j : Nat) (hj : j < h) (c : Letter) (v : Word Nat)
    (hv : (inputGrammar h D).Eligible v) (ha : markerName j c ∈ v) :
    (inputGrammar h D).gain v < (inputGrammar h D).gain (List.replicate 64 0) := by
  obtain ⟨left, right, he⟩ := List.append_of_mem (List.mem_range.mpr hj)
  have hnd : (List.range h).Nodup := List.nodup_range
  rw [he] at hnd
  have hnd' := List.nodup_append.mp hnd
  have hjleft : j ∉ left := by
    intro hm
    exact (List.disjoint_left.mp hnd'.2.2) hm (by simp)
  have hjright : j ∉ right := (List.nodup_cons.mp hnd'.2.1).1
  let targets := (targetNumbers h D).map (fun n => List.replicate n 0)
  let before := targets ++ left.map (inputAuxiliary h)
  let after := right.map (inputAuxiliary h)
  have hp : (inputPartition h D).pieces.Perm
      (before ++ [inputAuxiliary h j] ++ after) := by
    apply List.Perm.of_eq
    rw [inputPartition_pieces h D hh, he, List.map_append, List.map_cons]
    simp only [before, after, targets, List.append_assoc, List.singleton_append]
  have hbefore : ∀ w ∈ before, markerName j c ∉ w := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hw
      intro hm
      have hz := (List.mem_replicate.mp hm).2
      have hpos := markerName_pos j c
      omega
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
      exact marker_absent_other_auxiliary h j k c (by intro he; subst k; exact hjleft hk)
  have hafter : ∀ w ∈ after, markerName j c ∉ w := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
    exact marker_absent_other_auxiliary h j k c (by intro he; subst k; exact hjright hk)
  have hX : ∀ c : Letter, 0 ≠ markerName j c := by
    intro c he
    have hp := markerName_pos j c
    omega
  have hpow : 64*64^j = 64^(j+1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have hp' : (inputPartition h D).pieces.Perm
      (before ++ [(auxiliaryWord (64*64^j) (muIterate (auxiliaryExponent h (j+1)))).map
        (auxiliaryAlphabet 0 j)] ++ after) := by
    simpa only [hpow, inputAuxiliary] using hp
  exact (inputPartition h D).auxiliary_marker_loses h (j+1) (64^j) hh (by omega)
    (Nat.one_le_pow _ _ (by decide)) (auxiliaryAlphabet 0 j) (auxiliaryAlphabet_injective 0 j hX)
    before after hp' v hv (markerName j c) ha (by have := markerName_pos j c; exact Nat.ne_of_gt this)
    hbefore hafter

/-- Every maximizing eligible factor in the actual initial grammar is a^64.
This theorem is unconditional on any future phase invariant and is uniform
over every binary seed of the required length. -/
theorem input_maximizer_eq (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) (v : Word Nat) (hv : (inputGrammar h D).Eligible v)
    (hmax : ∀ u, (inputGrammar h D).Eligible u →
      (inputGrammar h D).gain u ≤ (inputGrammar h D).gain v) :
    v = List.replicate 64 0 := by
  have hbench : (inputGrammar h D).Eligible (List.replicate 64 0) := by
    apply (initialActiveStorage h D hh).benchmark_eligible
    rw [initialActiveStorage_current_length]
    have hp := auxiliaryLength_gt_mass h 1 hh hh
    omega
  have hm := hmax (List.replicate 64 0) hbench
  by_cases hall : ∀ a ∈ v, a = 0
  · have he : v = List.replicate v.length 0 := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
    by_cases hlen : v.length = 64
    · simpa [hlen] using he
    · have hv' : (inputGrammar h D).Eligible (List.replicate v.length 0) := by
        rw [← he]; exact hv
      have hl := inputGrammar_unary_loses h D hh hD v.length hlen hv'
      rw [← he] at hl
      omega
  · have hex : ∃ a ∈ v, a ≠ 0 := by
      by_contra hn
      apply hall
      intro a ha
      by_contra hne
      exact hn ⟨a, ha, hne⟩
    obtain ⟨a, ha, ha0⟩ := hex
    obtain ⟨j, hj, c, rfl⟩ := input_nonzero_factor_marker h D hh v hv a ha ha0
    have hl := input_marker_factor_loses h D hh j hj c v hv ha
    omega

theorem input_first_step {h : Nat} {D : List Bool} {H : Grammar}
    (hh : 1 ≤ h) (hD : D.length = h^2) (hs : GreedyStep (inputGrammar h D) H) :
    ∃ fresh, GlobalStep (inputGrammar h D) H (List.replicate 64 0) fresh
      (fun i => scanCount (List.replicate 64 0) ((inputGrammar h D).rhs i)) := by
  obtain ⟨v, fresh, hr, hv, hm⟩ := hs
  have he := input_maximizer_eq h D hh hD v hv hm
  subst v
  exact ⟨fresh, hr⟩

end GreedyLowerBound
