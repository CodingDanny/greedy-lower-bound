import GreedyLowerBound.ComparisonStart

set_option autoImplicit false
namespace GreedyLowerBound
open ComparisonIndex

def comparisonRhs (h : Nat) (D : List Bool) : ComparisonIndex → List (Nat ⊕ ComparisonIndex)
  | .target s k =>
    if prefixValue (chunk h D s) k = 0 then [Sum.inl 0]
    else List.replicate 64 (Sum.inr (target s (k-1))) ++
      (if ((chunk h D s)[k]?).getD false then [Sum.inl 0] else [])
  | .power j => List.replicate 64 (if j = 0 then Sum.inl 0 else Sum.inr (power (j-1)))
  | .aux j 0 c => [Sum.inr (power j), Sum.inl (markerName j c)]
  | .aux j (u+1) c => (mu c).map (fun d => Sum.inr (aux j u d))
  | .start => comparisonStartRhs h

def comparisonRank (h : Nat) : ComparisonIndex → Nat
  | .target _ k => k+1
  | .power j => j+1
  | .aux _ u _ => h+u+1
  | .start => 9*h+5

theorem comparisonTargetRefs_valid (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) (x : ComparisonIndex) (hx : x ∈ comparisonTargetRefs h) :
    ComparisonValid h D x ∧ x ≠ start := by
  obtain ⟨s, hs, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  have hs := List.mem_range.mp hs
  have hi := List.mem_range.mp hi
  have hp := targetNumber_positive h D s i hh hD hs
  have he : h+i+1 = h+1+i := by omega
  refine ⟨⟨hs, by omega, ?_⟩, by simp⟩
  simpa only [prefixValue, he, targetNumber] using hp

theorem comparisonRestRefs_valid (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) (x : ComparisonIndex) (hx : x ∈ comparisonRestRefs h) :
    ComparisonValid h D x ∧ x ≠ start := by
  rcases List.mem_append.mp hx with hx | hx
  · exact comparisonTargetRefs_valid h D hh hD x (List.mem_of_mem_tail hx)
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact ⟨⟨List.mem_range.mp hj, Nat.le_refl _⟩, by simp⟩

theorem comparisonRank_lt_start (h : Nat) (D : List Bool) (x : ComparisonIndex)
    (hx : ComparisonValid h D x) (hne : x ≠ start) : comparisonRank h x < comparisonRank h start := by
  cases x with
  | target s k => change s < h ∧ k < 2*h ∧ _ at hx; simp only [comparisonRank]; omega
  | power j => change j < h at hx; simp only [comparisonRank]; omega
  | aux j u c =>
    change j < h ∧ u ≤ auxiliaryExponent h (j+1) at hx
    unfold auxiliaryExponent at hx
    simp only [comparisonRank]
    omega
  | start => contradiction

theorem comparisonRhs_nonempty (h : Nat) (D : List Bool) (x : ComparisonIndex) :
    comparisonRhs h D x ≠ [] := by
  cases x with
  | target s k =>
    simp only [comparisonRhs]
    split_ifs <;> simp
  | power j => simp [comparisonRhs]
  | aux j u c =>
    cases u with
    | zero => simp [comparisonRhs]
    | succ u =>
      intro he
      have hh := congrArg List.length he
      simp only [comparisonRhs, List.length_map, mu_length, List.length_nil] at hh
      omega
  | start => simp [comparisonRhs, comparisonStartRhs]

theorem comparisonRhs_terminal_bound (h : Nat) (D : List Bool) (x : ComparisonIndex)
    (hx : ComparisonValid h D x) (a : Nat) (ha : Sum.inl a ∈ comparisonRhs h D x) :
    a < inputStart h D := by
  have hz : 0 < inputStart h D := by unfold inputStart; omega
  cases x with
  | target s k =>
    simp only [comparisonRhs] at ha
    split_ifs at ha <;> simp_all
  | power j =>
    by_cases hj : j = 0 <;> simp_all [comparisonRhs]
  | aux j u c =>
    cases u with
    | zero =>
      have he : a = markerName j c := by simpa [comparisonRhs] using ha
      rw [he]
      have hc := c.isLt
      have hj : j < h := hx.1
      unfold markerName inputStart
      omega
    | succ u => simp [comparisonRhs] at ha
  | start =>
    have ha' : Sum.inl a ∈ interleaveRefs (1+3*h) (comparisonRestRefs h) := by
      simpa [comparisonRhs, comparisonStartRhs] using ha
    have hb := (interleaveRefs_terminal (1+3*h) (comparisonRestRefs h) a ha').2
    rw [comparisonRestRefs_length] at hb
    unfold inputStart
    rwa [inputRest_length]

/-- Every right-hand-side reference names a defined earlier rule. -/
theorem comparisonRhs_reference (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) (x : ComparisonIndex) (hx : ComparisonValid h D x)
    (y : ComparisonIndex) (hy : Sum.inr y ∈ comparisonRhs h D x) :
    ComparisonValid h D y ∧ comparisonRank h y < comparisonRank h x := by
  cases x with
  | target s k =>
    by_cases hp : prefixValue (chunk h D s) k = 0
    · simp [comparisonRhs, hp] at hy
    · have he : y = target s (k-1) := by
        cases hb : ((chunk h D s)[k]?).getD false <;> simpa [comparisonRhs, hp, hb] using hy
      subst y
      have hk : 0 < k := by
        by_contra hn
        have he : k = 0 := by omega
        exact hp (by rw [he, prefixValue_zero])
      have hk' : k-1+1 = k := by omega
      change (s < h ∧ k-1 < 2*h ∧ 0 < prefixValue (chunk h D s) (k-1+1)) ∧ k-1+1 < k+1
      rw [hk']
      have hs : s < h ∧ k < 2*h ∧ _ := hx
      exact ⟨⟨hs.1, by omega, by omega⟩, by omega⟩
  | power j =>
    cases j with
    | zero => simp [comparisonRhs] at hy
    | succ j =>
      have he : y = power j := by simpa [comparisonRhs] using hy
      subst y
      change j+1 < h at hx
      exact ⟨by change j < h; omega, by simp [comparisonRank]⟩
  | aux j u c =>
    cases u with
    | zero =>
      have he : y = power j := by simpa [comparisonRhs] using hy
      subst y
      exact ⟨hx.1, by change j+1 < h+0+1; have hj := hx.1; omega⟩
    | succ u =>
      obtain ⟨d, hd, he⟩ := List.mem_map.mp hy
      have he' : aux j u d = y := Sum.inr.inj he
      subst y
      have hb : j < h ∧ u+1 ≤ auxiliaryExponent h (j+1) := hx
      exact ⟨⟨hb.1, by omega⟩, by simp [comparisonRank]⟩
  | start =>
    have hy' : y = target 0 h ∨ Sum.inr y ∈ interleaveRefs (1+3*h) (comparisonRestRefs h) := by
      simpa [comparisonRhs, comparisonStartRhs] using hy
    have hv : ComparisonValid h D y ∧ y ≠ start := by
      rcases hy' with rfl | hy'
      · have hm : target 0 h ∈ comparisonTargetRefs h :=
          List.mem_of_mem_head? (by rw [comparisonTargetRefs_head h hh]; simp)
        exact comparisonTargetRefs_valid h D hh hD _ hm
      · exact comparisonRestRefs_valid h D hh hD y
          ((interleaveRefs_reference _ _ _).mp hy')
    exact ⟨hv.1, comparisonRank_lt_start h D y hv.1 hv.2⟩

end GreedyLowerBound
