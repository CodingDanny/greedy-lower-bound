import GreedyLowerBound.Construction

set_option autoImplicit false

namespace GreedyLowerBound

def numberedRest (z : Nat) : List (Word Nat) → List (Nat × Word Nat)
  | [] => []
  | w::rest => (z,w)::numberedRest (z+1) rest

theorem numberedRest_words (z : Nat) (rest : List (Word Nat)) :
    (numberedRest z rest).map Prod.snd = rest := by
  induction rest generalizing z with
  | nil => rfl
  | cons w rest ih => simpa [numberedRest] using congrArg (List.cons w) (ih (z+1))

theorem numberedRest_indices (z : Nat) (rest : List (Word Nat)) :
    (numberedRest z rest).map Prod.fst = List.range' z rest.length := by
  induction rest generalizing z with
  | nil => rfl
  | cons w rest ih => simpa [numberedRest, List.range'_succ] using congrArg (List.cons z) (ih (z+1))

theorem numberedRest_mem (z : Nat) (rest : List (Word Nat)) (p : Nat × Word Nat)
    (hp : p ∈ numberedRest z rest) : z ≤ p.1 ∧ p.1 < z+rest.length ∧ p.2 ∈ rest := by
  have hi : p.1 ∈ List.range' z rest.length := by
    rw [← numberedRest_indices]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  have hw : p.2 ∈ rest := by
    rw [← numberedRest_words z rest]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  obtain ⟨i, hi, he⟩ := List.mem_range'.mp hi
  simp only [Nat.one_mul] at he
  exact ⟨by omega, by omega, hw⟩

theorem joinFragments_count_separator (first : Word Nat) (rest : List (Nat × Word Nat))
    (z : Nat) (hf : z ∉ first) (hr : ∀ p ∈ rest, z ∉ p.2) :
    (joinFragments first rest).count z = (rest.map Prod.fst).count z := by
  induction rest generalizing first with
  | nil => simp [joinFragments, List.count_eq_zero.mpr hf]
  | cons p rest ih =>
    have hp := hr p (by simp)
    have hh := ih p.2 hp (fun p hm => hr p (by simp [hm]))
    change (first ++ p.1 :: joinFragments p.2 rest).count z = _
    rw [List.count_append, List.count_eq_zero.mpr hf, Nat.zero_add]
    simp only [List.map_cons, List.count_cons, hh]

theorem numbered_join_separator (first : Word Nat) (rest : List (Word Nat)) (base k : Nat)
    (hk : k < rest.length) (hf : ∀ a ∈ first, a < base)
    (hr : ∀ w ∈ rest, ∀ a ∈ w, a < base) :
    (joinFragments first (numberedRest base rest)).count (base+k) = 1 := by
  rw [joinFragments_count_separator]
  · rw [numberedRest_indices]
    apply List.count_eq_one_of_mem
    · exact List.nodup_range'
    · exact List.mem_range'.mpr ⟨k, hk, by omega⟩
  · intro hm
    have hh := hf (base+k) hm
    omega
  · intro p hp hm
    have hh := hr p.2 (numberedRest_mem base rest p hp).2.2 (base+k) hm
    omega

theorem numbered_join_bound (first : Word Nat) (rest : List (Word Nat)) (base : Nat)
    (hf : ∀ a ∈ first, a < base) (hr : ∀ w ∈ rest, ∀ a ∈ w, a < base)
    (a : Nat) (ha : a ∈ joinFragments first (numberedRest base rest)) :
    a < base+rest.length := by
  rcases List.mem_append.mp ha with ha | ha
  · have hh := hf a ha
    omega
  · obtain ⟨p, hp, ha⟩ := List.mem_flatMap.mp ha
    have hm := numberedRest_mem base rest p hp
    rcases List.mem_cons.mp ha with ha | ha
    · simpa only [ha] using hm.2.1
    · have hh := hr p.2 hm.2.2 a ha
      omega

/-- Generic initial grammar for bounded-alphabet fragments and consecutively
numbered unique separators above that alphabet. -/
noncomputable def initialFragmentation (first : Word Nat) (rest : List (Word Nat))
    (base : Nat) (hf : ∀ a ∈ first, a < base)
    (hr : ∀ w ∈ rest, ∀ a ∈ w, a < base) :
    Fragmentation (Grammar.initial (joinFragments first (numberedRest base rest))
      (base+rest.length)) where
  first := first
  rest := numberedRest base rest
  start_mem := by simp [Grammar.initial]
  start_eq := by simp [Grammar.initial]
  separators := by
    intro p hp
    have hm := numberedRest_mem base rest p hp
    apply Grammar.initial_separator
    · have he : base+(p.1-base) = p.1 := by omega
      rw [← he]
      exact numbered_join_separator first rest base (p.1-base) (by omega) hf hr
    · omega

def inputFirst (h : Nat) (D : List Bool) : Word Nat :=
  List.replicate ((targetNumbers h D).headD 0) 0

def inputRest (h : Nat) (D : List Bool) : List (Word Nat) :=
  (targetNumbers h D).tail.map (fun n => List.replicate n 0) ++
    (List.range h).map (inputAuxiliary h)

def inputWord (h : Nat) (D : List Bool) : Word Nat :=
  joinFragments (inputFirst h D) (numberedRest (1+3*h) (inputRest h D))

def inputStart (h : Nat) (D : List Bool) : Nat := 1+3*h+(inputRest h D).length

def inputGrammar (h : Nat) (D : List Bool) : Grammar :=
  Grammar.initial (inputWord h D) (inputStart h D)

theorem inputAuxiliary_mem (h j a : Nat) (ha : a ∈ inputAuxiliary h j) :
    a = 0 ∨ ∃ c : Letter, a = markerName j c := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  obtain ⟨c, hc, hb⟩ := List.mem_flatMap.mp hb
  rcases List.mem_append.mp hb with hb | hb
  · have he := (List.mem_replicate.mp hb).2
    exact Or.inl (by simp [he, auxiliaryAlphabet])
  · have he : b = some c := by simpa using hb
    exact Or.inr ⟨c, by simp [he, auxiliaryAlphabet]⟩

theorem inputFirst_bound (h : Nat) (D : List Bool) (a : Nat) (ha : a ∈ inputFirst h D) :
    a < 1+3*h := by
  have he := (List.mem_replicate.mp ha).2
  omega

theorem inputRest_bound (h : Nat) (D : List Bool) (w : Word Nat) (hw : w ∈ inputRest h D)
    (a : Nat) (ha : a ∈ w) : a < 1+3*h := by
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hw
    have he := (List.mem_replicate.mp ha).2
    omega
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
    have hj' := List.mem_range.mp hj
    rcases inputAuxiliary_mem h j a ha with he | ⟨c, he⟩
    · omega
    · have hc := c.isLt
      simp only [markerName] at he
      omega

noncomputable def inputPartition (h : Nat) (D : List Bool) : Fragmentation (inputGrammar h D) :=
  initialFragmentation (inputFirst h D) (inputRest h D) (1+3*h)
    (inputFirst_bound h D) (inputRest_bound h D)

theorem inputWord_start_absent (h : Nat) (D : List Bool) : inputStart h D ∉ inputWord h D := by
  intro hm
  have hh := numbered_join_bound (inputFirst h D) (inputRest h D) (1+3*h)
    (inputFirst_bound h D) (inputRest_bound h D) (inputStart h D) hm
  exact Nat.lt_irrefl _ hh

theorem inputGrammar_generates (h : Nat) (D : List Bool) :
    (inputGrammar h D).Generates (inputWord h D) :=
  Grammar.initial_generates _ _ (inputWord_start_absent h D)

theorem inputFirst_nonempty (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) : inputFirst h D ≠ [] := by
  have hlen := targetNumbers_length h D
  have hpos : 0 < (targetNumbers h D).length := by rw [hlen]; exact Nat.pow_pos (by omega)
  have hne := List.length_pos_iff.mp hpos
  have hm : (targetNumbers h D).headD 0 ∈ targetNumbers h D := by
    cases he : targetNumbers h D with
    | nil => exact False.elim (hne he)
    | cons a w => simp
  have hp := targetNumbers_positive h D hh hD _ hm
  apply List.length_pos_iff.mp
  simpa only [inputFirst, List.length_replicate] using hp

theorem inputWord_nonempty (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) : inputWord h D ≠ [] := by
  intro he
  have hz := List.append_eq_nil_iff.mp he
  exact inputFirst_nonempty h D hh hD hz.1

theorem inputGrammar_wellFormed (h : Nat) (D : List Bool) (hh : 1 ≤ h)
    (hD : D.length = h^2) : (inputGrammar h D).WellFormed :=
  Grammar.initial_wellFormed _ _ (inputWord_nonempty h D hh hD) (inputWord_start_absent h D)

theorem inputPartition_pieces (h : Nat) (D : List Bool) (hh : 1 ≤ h) :
    (inputPartition h D).pieces =
      (targetNumbers h D).map (fun n => List.replicate n 0) ++
        (List.range h).map (inputAuxiliary h) := by
  have hn : targetNumbers h D ≠ [] := by
    intro he
    have hl := targetNumbers_length h D
    have hp : 0 < h^2 := Nat.pow_pos (by omega)
    simp only [he, List.length_nil] at hl
    omega
  have hparts : (inputPartition h D).pieces = inputFirst h D :: inputRest h D := by
    simp [Fragmentation.pieces, inputPartition, initialFragmentation,
      inputGrammar, Grammar.initial, numberedRest_words]
  rw [hparts]
  unfold inputFirst inputRest
  cases he : targetNumbers h D with
  | nil => exact False.elim (hn he)
  | cons n ns => simp

theorem targetNumbers_head_mem (h : Nat) (D : List Bool) (hh : 1 ≤ h) :
    (targetNumbers h D).headD 0 ∈ targetNumbers h D := by
  have hn : targetNumbers h D ≠ [] := by
    intro he
    have hl := targetNumbers_length h D
    have hp : 0 < h^2 := Nat.pow_pos (by omega)
    simp only [he, List.length_nil] at hl
    omega
  cases he : targetNumbers h D with
  | nil => exact False.elim (hn he)
  | cons a w => simp

end GreedyLowerBound
