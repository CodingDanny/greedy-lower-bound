import GreedyLowerBound.PhaseCleanup
import Mathlib.Logic.Equiv.Basic

set_option autoImplicit false

namespace GreedyLowerBound

/-- Replace the as-yet-unused placeholder A(t+1) by the fresh primary name.
Swapping symbol names keeps the whole indexing function injective. All
already-created primary names are proved fixed below. -/
def advancePrimaries (A : Nat → Nat) (t fresh : Nat) : Nat → Nat :=
  fun i => Equiv.swap (A (t+1)) fresh (A i)

theorem advancePrimaries_injective (A : Nat → Nat) (hA : Function.Injective A)
    (t fresh : Nat) : Function.Injective (advancePrimaries A t fresh) :=
  (Equiv.swap (A (t+1)) fresh).injective.comp hA

theorem advancePrimaries_new (A : Nat → Nat) (t fresh : Nat) :
    advancePrimaries A t fresh (t+1) = fresh := Equiv.swap_apply_left _ _

theorem advancePrimaries_old (A : Nat → Nat) (hA : Function.Injective A)
    (t fresh : Nat) (hf : ∀ i ≤ t, fresh ≠ A i) (i : Nat) (hi : i ≤ t) :
    advancePrimaries A t fresh i = A i :=
  Equiv.swap_apply_of_ne_of_ne (by intro he; have hh := hA he; omega) (Ne.symm (hf i hi))

theorem lowerDigits_congr (n : Nat) (A B : Nat → Nat) (t : Nat)
    (hAB : ∀ i < t, A i = B i) : lowerDigits n A t = lowerDigits n B t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [lowerDigits, lowerDigits, hAB t (by omega), ih (fun i hi => hAB i (by omega))]

theorem targetState_congr (n : Nat) (A B : Nat → Nat) (t : Nat)
    (hAB : ∀ i ≤ t, A i = B i) : targetState n A t = targetState n B t := by
  rw [targetState, targetState, hAB t (Nat.le_refl _),
    lowerDigits_congr n A B t (fun i hi => hAB i (by omega))]

theorem scanOutput_target_advance (n : Nat) (A : Nat → Nat) (hA : Function.Injective A)
    (t fresh : Nat) (hf : ∀ i ≤ t, fresh ≠ A i) :
    scanOutput (List.replicate 64 (A t)) fresh (targetState n A t) =
      targetState n (advancePrimaries A t fresh) (t+1) := by
  let B := advancePrimaries A t fresh
  have hB := advancePrimaries_injective A hA t fresh
  have he := targetState_congr n B A t (advancePrimaries_old A hA t fresh hf)
  have hs := targetState_advance n B t hB
  rw [he] at hs
  dsimp only [B] at hs
  rw [advancePrimaries_old A hA t fresh hf t (Nat.le_refl _), advancePrimaries_new] at hs
  exact (hs.output_eq (by simp)).symm

theorem scanOutput_padded_advance (X fresh k : Nat) (markers : Word Nat)
    (hm : ∀ z ∈ markers, z ≠ X) :
    scanOutput (List.replicate 64 X) fresh (paddedRuns X (64*k) markers) =
      paddedRuns fresh k markers := by
  have hs := Scan.padded_word 64 k X fresh markers (by decide) hm
  rw [Nat.mul_comm k 64] at hs
  exact (hs.output_eq (by simp)).symm

theorem paddedRuns_one_noAdjacent (X : Nat) (markers : Word Nat)
    (hm : ∀ z ∈ markers, z ≠ X) : NoAdjacent X (paddedRuns X 1 markers) := by
  induction markers with
  | nil => simp [paddedRuns, NoAdjacent]
  | cons z markers ih =>
    have hz := hm z (by simp)
    have ht := ih (fun a ha => hm a (by simp [ha]))
    change NoAdjacent X (X::z::paddedRuns X 1 markers)
    apply (noAdjacent_cons_iff X X _).mpr
    refine ⟨?_, (noAdjacent_cons_iff X z _).mpr ⟨fun he => False.elim (hz he), ht⟩⟩
    intro _ hp
    exact hz (List.cons_prefix_cons.mp hp).1.symm

def unsetOwner (owner : Nat → Option StorageClass) (fresh : Nat) : Nat → Option StorageClass :=
  fun a => if a = fresh then none else owner a

theorem UsesOnePrimary.unset {owner : Nat → Option StorageClass} {C : StorageClass}
    {X fresh : Nat} {w : Word Nat} (hw : UsesOnePrimary owner C X w) (hf : fresh ∉ w) :
    UsesOnePrimary (unsetOwner owner fresh) C X w := by
  intro a ha
  have he : a ≠ fresh := by intro he; subst a; exact hf ha
  rcases hw a ha with he' | ho
  · exact Or.inl he'
  · exact Or.inr (by simp only [unsetOwner, if_neg he, ho])

namespace PhaseStorage

theorem scanned_unfinished {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (ht : t < h) (fresh : Nat) :
    (unfinishedCells h t S.primary).map (scanOutput (List.replicate 64 (S.primary t)) fresh) =
      paddedRuns fresh 1 (auxiliaryMarkers h t) ::
        (List.range (h-(t+1))).map (fun s =>
          paddedRuns fresh (64^(s+1)) (auxiliaryMarkers h ((t+1)+s))) := by
  rw [S.unfinished_split ht, List.map_cons, List.map_map]
  have hcur := scanOutput_padded_advance (S.primary t) fresh 1 (auxiliaryMarkers h t)
    (S.active_ne_markers t ht)
  norm_num only at hcur
  rw [hcur]
  congr 1
  have he : h-t-1 = h-(t+1) := by omega
  rw [he]
  apply List.map_congr_left
  intro s hs
  have hi := List.mem_range.mp hs
  have hidx : t+(s+1) = (t+1)+s := by omega
  simp only [Function.comp_def, hidx]
  exact scanOutput_padded_advance (S.primary t) fresh (64^(s+1)) _
    (S.active_ne_markers ((t+1)+s) (by omega))

theorem scanned_cleanup {G : Grammar} {h t : Nat} {D : List Bool}
    (S : PhaseStorage G h D t) (fresh : Nat) (w : Word Nat)
    (hw : w ∈ S.finished.map Prod.snd ++ S.powers.map Prod.snd) :
    scanOutput (List.replicate 64 (S.primary t)) fresh w = w :=
  scanOutput_eq_self _ fresh w (by simp)
    (scanCount_zero_of_noAdjacent (S.primary t) 64 w (by decide) (S.cleanup_no_active_adjacent w hw))

end PhaseStorage

end GreedyLowerBound
