import GreedyLowerBound.Separators

set_option autoImplicit false

namespace GreedyLowerBound

universe u
variable {α : Type u} [DecidableEq α]

/-- A factor avoiding a delimiter cannot start before that delimiter and
finish after it. No uniqueness assumption on the delimiter is needed here. -/
theorem prefix_before_separator (v pre post : Word α) (z : α) (hz : z ∉ v) :
    v.IsPrefix (pre ++ z :: post) ↔ v.IsPrefix pre := by
  induction pre generalizing v with
  | nil =>
    cases v with
    | nil => simp
    | cons a v =>
      constructor
      · intro hp
        have he : a = z := (List.cons_prefix_cons.mp hp).1
        subst a
        exact False.elim (hz (by simp))
      · simp
  | cons a pre ih =>
    cases v with
    | nil => simp
    | cons b v =>
      simp only [List.cons_append, List.cons_prefix_cons]
      constructor
      · rintro ⟨he, hp⟩
        exact ⟨he, (ih v (fun hm => hz (by simp [hm]))).mp hp⟩
      · rintro ⟨he, hp⟩
        exact ⟨he, (ih v (fun hm => hz (by simp [hm]))).mpr hp⟩

theorem Scan.append_separator {v s t s' t' : Word α} {fresh z : α} {c c' : Nat}
    (h : Scan v fresh s t c) (h' : Scan v fresh s' t' c') (hv : v ≠ []) (hz : z ∉ v) :
    Scan v fresh (s ++ z :: s') (t ++ z :: t') (c + c') := by
  induction h with
  | nil =>
    have hn : ¬ v.IsPrefix (z :: s') := by
      intro hp
      cases v with
      | nil =>
        exact False.elim (hv rfl)
      | cons a v =>
        have he := (List.cons_prefix_cons.mp hp).1
        subst a
        exact hz (by simp)
    simpa using Scan.skip hn h'
  | hit h ih =>
    simpa only [List.append_assoc, List.cons_append, Nat.add_assoc,
      Nat.add_comm 1 c'] using Scan.hit ih
  | skip hn h ih =>
    have hn' : ¬ v.IsPrefix ((_ :: _) ++ z :: s') :=
      fun hp => hn ((prefix_before_separator v _ s' z hz).mp hp)
    simpa only [List.cons_append] using Scan.skip hn' ih

/-- A full scan has a unique output, including the literal positions of the
fresh symbols. Counting alone would not suffice to update a phase invariant. -/
theorem Scan.output_unique_of_eq {v s s' t t' : Word α} {fresh : α} {c c' : Nat}
    (h : Scan v fresh s t c) (h' : Scan v fresh s' t' c')
    (hv : v ≠ []) (he : s = s') : t = t' := by
  induction h generalizing s' t' c' with
  | nil =>
    cases h' with
    | nil => rfl
    | hit h' =>
      have hl := congrArg List.length he
      have hvp := List.length_pos_iff.mpr hv
      simp only [List.length_nil, List.length_append] at hl
      omega
    | skip hn h' => simp at he
  | @hit s t c h ih =>
    cases h' with
    | nil =>
      have hl := congrArg List.length he
      have hvp := List.length_pos_iff.mpr hv
      simp only [List.length_nil, List.length_append] at hl
      omega
    | hit h' =>
      exact congrArg (List.cons fresh) (ih h' (List.append_cancel_left he))
    | skip hn h' =>
      exact False.elim (hn (he ▸ List.prefix_append _ _))
  | @skip a s t c hn h ih =>
    cases h' with
    | nil => simp at he
    | hit h' => exact False.elim (hn (he.symm ▸ List.prefix_append _ _))
    | skip hn' h' =>
      have hh := List.cons.inj he
      rw [← hh.1]
      exact congrArg (List.cons a) (ih h' hh.2)

theorem Scan.output_unique {v s t t' : Word α} {fresh : α} {c c' : Nat}
    (h : Scan v fresh s t c) (h' : Scan v fresh s t' c') (hv : v ≠ []) : t = t' :=
  h.output_unique_of_eq h' hv rfl

theorem scanCount_append_separator (v pre post : Word α) (z : α)
    (hv : v ≠ []) (hz : z ∉ v) :
    scanCount v (pre ++ z :: post) = scanCount v pre + scanCount v post := by
  obtain ⟨t, ht⟩ := Scan.exists_output v pre z hv
  obtain ⟨t', ht'⟩ := Scan.exists_output v post z hv
  exact ((ht.append_separator ht' hv hz).count_eq hv).symm

/-- Splitting an actual scan at a protected delimiter gives the actual scans
on both sides, with exactly additive counts. -/
theorem Scan.split_separator {v pre post out : Word α} {fresh z : α} {c : Nat}
    (h : Scan v fresh (pre ++ z :: post) out c) (hv : v ≠ []) (hz : z ∉ v) :
    ∃ left right c₁ c₂, Scan v fresh pre left c₁ ∧ Scan v fresh post right c₂ ∧
      out = left ++ z :: right ∧ c = c₁ + c₂ := by
  obtain ⟨left, hl⟩ := Scan.exists_output v pre fresh hv
  obtain ⟨right, hr⟩ := Scan.exists_output v post fresh hv
  have hc := hl.append_separator hr hv hz
  exact ⟨left, right, _, _, hl, hr, h.output_unique hc hv, h.count_unique hc hv⟩

/-- The start rule consists of one first fragment, then delimiter-fragment
pairs. This representation permits empty fragments and distinct delimiters. -/
def joinFragments (first : Word α) (rest : List (α × Word α)) : Word α :=
  first ++ rest.flatMap (fun p => p.1 :: p.2)

theorem scanCount_joinFragments (v first : Word α) (rest : List (α × Word α))
    (hv : v ≠ []) (hz : ∀ p ∈ rest, p.1 ∉ v) :
    scanCount v (joinFragments first rest) =
      scanCount v first + (rest.map (fun p => scanCount v p.2)).sum := by
  induction rest generalizing first with
  | nil => simp [GreedyLowerBound.joinFragments]
  | cons p rest ih =>
    have hp := hz p (by simp)
    have hrest : ∀ p ∈ rest, p.1 ∉ v := fun p hm => hz p (by simp [hm])
    change scanCount v (first ++ p.1 :: joinFragments p.2 rest) = _
    rw [scanCount_append_separator v first _ p.1 hv hp, ih p.2 hrest]
    simp [Nat.add_assoc]

/-- Simultaneous fragment scans reconstruct the global start-rule scan. -/
theorem Scan.joinFragments {v first first' : Word α} {fresh : α} {c : Nat}
    (h : Scan v fresh first first' c)
    (rest : List (α × Word α)) (next : α × Word α → Word α)
    (hv : v ≠ []) (hz : ∀ p ∈ rest, p.1 ∉ v)
    (hs : ∀ p ∈ rest, Scan v fresh p.2 (next p) (scanCount v p.2)) :
    Scan v fresh (joinFragments first rest)
      (joinFragments first' (rest.map (fun p => (p.1, next p))))
      (c + (rest.map (fun p => scanCount v p.2)).sum) := by
  induction rest generalizing first first' c with
  | nil => simpa [GreedyLowerBound.joinFragments] using h
  | cons p rest ih =>
    have hp := hs p (by simp)
    have hr := ih hp (fun p hm => hz p (by simp [hm]))
      (fun p hm => hs p (by simp [hm]))
    have hh := h.append_separator hr hv (hz p (by simp))
    simpa only [GreedyLowerBound.joinFragments, List.flatMap_cons, List.map_cons, List.sum_cons,
      List.cons_append, Nat.add_assoc] using hh

end GreedyLowerBound
