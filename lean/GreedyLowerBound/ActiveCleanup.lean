import GreedyLowerBound.FragmentUpdate

set_option autoImplicit false

namespace GreedyLowerBound

theorem scanOutput_eq_self (v : Word Nat) (fresh : Nat) (w : Word Nat)
    (hv : v ≠ []) (hc : scanCount v w = 0) : scanOutput v fresh w = w :=
  ((scanOutput_spec v fresh w hv).zero_eq hc).symm

namespace ActiveStorage

def protectedCells {G : Grammar} {X : Nat} (S : ActiveStorage G X) : List (Word Nat) :=
  S.targets ++ [paddedRuns X 64 S.current] ++
    S.later.map (fun p => paddedRuns X (64*p.1) p.2)

theorem cleanup_contains_selected {G : Grammar} {X : Nat} (S : ActiveStorage G X)
    (v : Word Nat) (hv : G.Eligible v)
    (hp : ∀ w ∈ S.protectedCells, scanCount v w = 0) :
    ∃ w ∈ S.cleanup, v.IsInfix w := by
  have hvn : v ≠ [] := by intro he; have hh := hv.1; simp [he] at hh
  have he := S.partition.frequency_eq v hv
  rw [(S.cells.map (scanCount v)).sum_eq] at he
  have hz : cellFrequency S.protectedCells v = 0 := by
    unfold cellFrequency
    apply List.sum_eq_zero
    intro n hn
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hn
    exact hp w hw
  change G.frequency v = cellFrequency (S.protectedCells ++ S.cleanup) v at he
  rw [cellFrequency_append, hz, Nat.zero_add] at he
  have hc : 0 < cellFrequency S.cleanup v := by rw [← he]; have := hv.2; omega
  have hex : ∃ w ∈ S.cleanup, 0 < scanCount v w := by
    by_contra hn
    have hzero : cellFrequency S.cleanup v = 0 := by
      unfold cellFrequency
      apply List.sum_eq_zero
      intro n hn'
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hn'
      by_contra he
      exact hn ⟨w, hw, by omega⟩
    omega
  obtain ⟨w, hw, hc⟩ := hex
  exact ⟨w, hw, (scanCount_is_maximum v w hvn).1.factor_isInfix hc⟩

/-- Once competitor exclusion establishes that the protected cells are
untouched, all parts of the active-unary storage invariant survive cleanup.
In particular the fresh right-hand side is included in cleanup storage. -/
noncomputable def afterCleanup {G H : Grammar} {X : Nat} (S : ActiveStorage G X)
    {v : Word Nat} {fresh : Nat} {counts : Nat → Nat}
    (hr : GlobalStep G H v fresh counts) (hv : G.Eligible v) (hf : fresh ≠ X)
    (hp : ∀ w ∈ S.protectedCells, scanCount v w = 0) : ActiveStorage H X := by
  have hvn : v ≠ [] := by intro he; have hh := hv.1; simp [he] at hh
  have hmap : S.protectedCells.map (scanOutput v fresh) = S.protectedCells := by
    calc
      _ = S.protectedCells.map id := List.map_congr_left (fun w hw =>
        scanOutput_eq_self v fresh w hvn (hp w hw))
      _ = _ := List.map_id _
  refine {
    partition := S.partition.afterStep hr hv
    targets := S.targets
    current := S.current
    later := S.later
    cleanup := S.cleanup.map (scanOutput v fresh) ++ [v]
    current_markers := S.current_markers
    later_markers := S.later_markers
    cleanup_noAdjacent := ?_
    cells := ?_ }
  · intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hw
      exact (scanOutput_spec v fresh old hvn).preserves_noAdjacent hf
        (S.cleanup_noAdjacent old hold)
    · have he : w = v := by simpa using hw
      subst w
      obtain ⟨old, hold, hin⟩ := S.cleanup_contains_selected v hv hp
      exact (S.cleanup_noAdjacent old hold).of_infix hin
  · have h1 := S.partition.afterStep_pieces hr hv
    have h2 := (S.cells.map (scanOutput v fresh)).append_right [v]
    have h3 := h1.trans h2
    change ((S.partition.afterStep hr hv).pieces).Perm
      ((S.protectedCells ++ S.cleanup).map (scanOutput v fresh) ++ [v]) at h3
    rw [List.map_append, hmap, List.append_assoc] at h3
    exact h3

theorem afterCleanup_targets {G H : Grammar} {X : Nat} (S : ActiveStorage G X)
    {v : Word Nat} {fresh : Nat} {counts : Nat → Nat}
    (hr : GlobalStep G H v fresh counts) (hv : G.Eligible v) (hf : fresh ≠ X)
    (hp : ∀ w ∈ S.protectedCells, scanCount v w = 0) :
    (S.afterCleanup hr hv hf hp).targets = S.targets := rfl

theorem afterCleanup_current {G H : Grammar} {X : Nat} (S : ActiveStorage G X)
    {v : Word Nat} {fresh : Nat} {counts : Nat → Nat}
    (hr : GlobalStep G H v fresh counts) (hv : G.Eligible v) (hf : fresh ≠ X)
    (hp : ∀ w ∈ S.protectedCells, scanCount v w = 0) :
    (S.afterCleanup hr hv hf hp).current = S.current := rfl

theorem afterCleanup_later {G H : Grammar} {X : Nat} (S : ActiveStorage G X)
    {v : Word Nat} {fresh : Nat} {counts : Nat → Nat}
    (hr : GlobalStep G H v fresh counts) (hv : G.Eligible v) (hf : fresh ≠ X)
    (hp : ∀ w ∈ S.protectedCells, scanCount v w = 0) :
    (S.afterCleanup hr hv hf hp).later = S.later := rfl

end ActiveStorage

end GreedyLowerBound
