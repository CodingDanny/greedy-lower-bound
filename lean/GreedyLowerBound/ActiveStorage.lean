import GreedyLowerBound.FragmentAccounting
import GreedyLowerBound.PhaseEstimates

set_option autoImplicit false

namespace GreedyLowerBound

def paddedRuns (X L : Nat) (w : Word Nat) : Word Nat :=
  w.flatMap (fun z => List.replicate L X ++ [z])

theorem scanCount_paddedRuns (X d L : Nat) (w : Word Nat) (hd : 0 < d)
    (hw : ∀ z ∈ w, z ≠ X) :
    scanCount (List.replicate d X) (paddedRuns X L w) = w.length * (L / d) := by
  have hv : List.replicate d X ≠ [] := by simp; omega
  induction w with
  | nil => simp [paddedRuns, scanCount, hv]
  | cons z w ih =>
    have hz : z ∉ List.replicate d X := by
      simp only [List.mem_replicate, not_and]
      exact fun _ => hw z (by simp)
    simp only [paddedRuns, List.flatMap_cons, List.append_assoc, List.singleton_append]
    change scanCount (List.replicate d X)
      (List.replicate L X ++ z :: paddedRuns X L w) = _
    rw [scanCount_append_separator _ _ _ z hv hz, scanCount_replicate d L X hd,
      ih (fun a ha => hw a (by simp [ha]))]
    simp [Nat.add_mul, Nat.add_comm]

theorem auxiliaryWord_renamed (L : Nat) (w : Word Letter) (f : Option Letter → Nat) :
    (auxiliaryWord L w).map f = paddedRuns (f none) L (w.map (fun a => f (some a))) := by
  simp [auxiliaryWord, paddedRuns, List.map_flatMap, List.flatMap_map,
    List.map_replicate, Function.comp_def]

/-- No adjacent copies of X in literal storage. This property concerns the
unexpanded grammar and therefore survives introduction of private symbols. -/
def NoAdjacent (X : Nat) (w : Word Nat) : Prop :=
  ¬ [X, X].IsInfix w

theorem scanCount_zero_of_noAdjacent (X d : Nat) (w : Word Nat) (hd : 2 ≤ d)
    (hw : NoAdjacent X w) : scanCount (List.replicate d X) w = 0 := by
  have hv : List.replicate d X ≠ [] := by simp; omega
  by_contra hc
  have hp := (scanCount_is_maximum (List.replicate d X) w hv).1
  generalize he : scanCount (List.replicate d X) w = c at hp
  cases c with
  | zero => omega
  | succ c =>
    cases hp with
    | next pre rest ht =>
      apply hw
      have hd' : d = 2 + (d-2) := by omega
      rw [hd', List.replicate_add, List.append_assoc]
      exact ⟨pre, List.replicate (d-2) X ++ rest, by simp [List.append_assoc]⟩

/-- The part of the phase invariant needed for unary competitors. It is
literal and exhaustive: permutation of `pieces` accounts for every fragment
and every non-start rule, including all cleanup definitions. -/
structure ActiveStorage (G : Grammar) (X : Nat) where
  partition : Fragmentation G
  targets : List (Word Nat)
  current : Word Nat
  later : List (Nat × Word Nat)
  cleanup : List (Word Nat)
  current_markers : ∀ z ∈ current, z ≠ X
  later_markers : ∀ p ∈ later, ∀ z ∈ p.2, z ≠ X
  cleanup_noAdjacent : ∀ w ∈ cleanup, NoAdjacent X w
  cells : partition.pieces.Perm (targets ++ [paddedRuns X 64 current] ++
    later.map (fun p => paddedRuns X (64*p.1) p.2) ++ cleanup)

namespace ActiveStorage

theorem benchmark_eligible {G : Grammar} {X : Nat} (S : ActiveStorage G X)
    (hM : 2 ≤ S.current.length) : G.Eligible (List.replicate 64 X) := by
  have hw : paddedRuns X 64 S.current ∈ S.partition.pieces :=
    S.cells.mem_iff.mpr (by simp)
  have hf := S.partition.scanCount_le_frequency (List.replicate 64 X)
    (paddedRuns X 64 S.current) (by simp) hw
  rw [scanCount_paddedRuns X 64 64 S.current (by decide) S.current_markers] at hf
  refine ⟨by simp, ?_⟩
  norm_num only at hf
  rw [Nat.mul_one] at hf
  exact hM.trans hf

def laterCount {G : Grammar} {X : Nat} (S : ActiveStorage G X) (d : Nat) : Nat :=
  (S.later.map (fun p => p.2.length * (64*p.1/d))).sum

def laterMass {G : Grammar} {X : Nat} (S : ActiveStorage G X) : Nat :=
  (S.later.map (fun p => p.2.length * (64*p.1))).sum

theorem frequency_eq {G : Grammar} {X : Nat} (S : ActiveStorage G X) (d : Nat)
    (hv : G.Eligible (List.replicate d X)) :
    G.frequency (List.replicate d X) = cellFrequency S.targets (List.replicate d X) +
      S.current.length*(64/d) + S.laterCount d := by
  have hd : 2 ≤ d := by simpa using hv.1
  rw [S.partition.frequency_eq _ hv]
  have hp := (S.cells.map (scanCount (List.replicate d X))).sum_eq
  rw [hp]
  have hz : cellFrequency S.cleanup (List.replicate d X) = 0 := by
    unfold cellFrequency
    apply List.sum_eq_zero
    intro n hn
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hn
    exact scanCount_zero_of_noAdjacent X d w hd (S.cleanup_noAdjacent w hw)
  change cellFrequency (_ ++ _ ++ _ ++ _) _ = _
  rw [cellFrequency_append, cellFrequency_append, cellFrequency_append, hz]
  simp only [cellFrequency, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, scanCount_paddedRuns X d 64 S.current (by omega) S.current_markers]
  congr 1
  unfold laterCount
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  exact scanCount_paddedRuns X d (64*p.1) p.2 (by omega) (S.later_markers p hp)

theorem current_le_frequency {G : Grammar} {X : Nat} (S : ActiveStorage G X)
    (hv : G.Eligible (List.replicate 64 X)) :
    S.current.length ≤ G.frequency (List.replicate 64 X) := by
  rw [S.frequency_eq 64 hv]
  simp only [Nat.div_self (by decide : 0 < 64), Nat.mul_one]
  omega

theorem later_shorter_benefit {G : Grammar} {X : Nat} (S : ActiveStorage G X)
    (d : Nat) (hd : 2 ≤ d) (hdB : d ≤ 64) :
    S.laterCount d * (d-1) ≤ S.laterCount 64 * 63 := by
  unfold laterCount
  induction S.later with
  | nil => simp
  | cons p rest ih =>
    have h := divisible_run_shorter_benefit 64 d p.1 hd hdB
    have hm := Nat.mul_le_mul_left p.2.length h
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    have hdiv : 64*p.1/64 = p.1 := by omega
    rw [Nat.mul_comm p.1 64] at hm
    simp only [hdiv, Nat.mul_assoc] at *
    norm_num only at hm
    omega

theorem later_covered_mass {G : Grammar} {X : Nat} (S : ActiveStorage G X)
    (d : Nat) : S.laterCount d * d ≤ S.laterMass := by
  unfold laterCount laterMass
  induction S.later with
  | nil => simp
  | cons p rest ih =>
    have hm := Nat.mul_le_mul_left p.2.length (Nat.div_mul_le_self (64*p.1) d)
    simp only [List.map_cons, List.sum_cons, Nat.add_mul, Nat.mul_assoc] at *
    omega

/-- The full grammar-wide inequality (16), with all cleanup storage included
in `S.cells`. The only numerical hypothesis is the advertised scale gap. -/
theorem shorter_unary_loses {G : Grammar} {X : Nat} (S : ActiveStorage G X)
    (H d : Nat) (hH : cellMass S.targets ≤ H)
    (hM : H + 64 < S.current.length) (hd : 2 ≤ d) (hdB : d < 64)
    (hv : G.Eligible (List.replicate d X)) :
    G.gain (List.replicate d X) < G.gain (List.replicate 64 X) := by
  have hb := S.benchmark_eligible (by omega)
  have hfd := S.frequency_eq d hv
  have hfB := S.frequency_eq 64 hb
  have ht := cellFrequency_covered_length_le S.targets (List.replicate d X)
  simp only [List.length_replicate] at ht
  have ht' : cellFrequency S.targets (List.replicate d X)*(d-1) ≤ H :=
    (Nat.mul_le_mul_left _ (Nat.sub_le d 1)).trans (ht.trans hH)
  have hcurr := Nat.mul_le_mul_left S.current.length
    (shorter_unary_run_advantage 64 d hd hdB)
  have hlater := S.later_shorter_benefit d hd (by omega)
  have htotal : G.frequency (List.replicate d X)*(d-1) + S.current.length ≤
      G.frequency (List.replicate 64 X)*63 + H := by
    rw [hfd, hfB]
    simp only [Nat.mul_add, Nat.mul_one] at hcurr
    norm_num only at hcurr ⊢
    simp only [Nat.add_mul, Nat.mul_assoc]
    omega
  have hi := Int.ofNat_le.mpr htotal
  have hd' : (1 : Int) ≤ d := by omega
  push_cast at hi
  rw [Int.natCast_sub (by omega : 1 ≤ d)] at hi
  change (G.frequency (List.replicate d X) : Int)*((d : Int)-1) + S.current.length ≤
    (G.frequency (List.replicate 64 X) : Int)*63 + H at hi
  simp only [Grammar.gain, List.length_replicate]
  change (G.frequency (List.replicate d X) : Int)*((d : Int)-1) - d <
    (G.frequency (List.replicate 64 X) : Int)*63 - 64
  omega

/-- The long unary case (17): current runs are too short, and later active
mass together with target mass is below the benchmark. -/
theorem longer_unary_loses {G : Grammar} {X : Nat} (S : ActiveStorage G X)
    (H d : Nat) (hH : cellMass S.targets ≤ H)
    (hM : H + 64 < S.current.length) (hL : S.laterMass < 2*S.current.length)
    (hdB : 64 < d) (hv : G.Eligible (List.replicate d X)) :
    G.gain (List.replicate d X) < G.gain (List.replicate 64 X) := by
  have hb := S.benchmark_eligible (by omega)
  have hfd := S.frequency_eq d hv
  have hfB := S.current_le_frequency hb
  have ht := cellFrequency_covered_length_le S.targets (List.replicate d X)
  simp only [List.length_replicate] at ht
  have hl := S.later_covered_mass d
  have hcover : G.frequency (List.replicate d X)*d < H + 2*S.current.length := by
    rw [hfd, Nat.div_eq_of_lt hdB]
    simp only [Nat.mul_zero, Nat.add_zero, Nat.add_mul]
    omega
  have hi := Int.ofNat_lt.mpr hcover
  have hc : (0 : Int) ≤ G.frequency (List.replicate d X) := Int.natCast_nonneg _
  simp only [Grammar.gain, List.length_replicate]
  push_cast at hi
  change (G.frequency (List.replicate d X) : Int)*((d : Int)-1) - d <
    (G.frequency (List.replicate 64 X) : Int)*63 - 64
  have hfB' := Int.ofNat_le.mpr hfB
  have hM' : (H : Int) + 64 < S.current.length := by omega
  have hd' : (64 : Int) < d := by omega
  nlinarith

theorem unary_loses {G : Grammar} {X : Nat} (S : ActiveStorage G X)
    (H d : Nat) (hH : cellMass S.targets ≤ H)
    (hM : H + 64 < S.current.length) (hL : S.laterMass < 2*S.current.length)
    (hd : d ≠ 64) (hv : G.Eligible (List.replicate d X)) :
    G.gain (List.replicate d X) < G.gain (List.replicate 64 X) := by
  have hlen : 2 ≤ d := by simpa using hv.1
  rcases lt_or_gt_of_ne hd with hd | hd
  · exact S.shorter_unary_loses H d hH hM hlen hd hv
  · exact S.longer_unary_loses H d hH hM hL hd hv

end ActiveStorage

end GreedyLowerBound
