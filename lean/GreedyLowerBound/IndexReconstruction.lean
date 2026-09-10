import GreedyLowerBound.DigitWindows

set_option autoImplicit false
namespace GreedyLowerBound

theorem oneIndices_mem_lt (w : List Bool) (a : Nat) (ha : a ∈ oneIndices w) :
    a < w.length := by
  induction w with
  | nil => simp [oneIndices] at ha
  | cons b w ih =>
    simp only [oneIndices, List.mem_append] at ha
    rcases ha with ha | ha
    · have he : a = w.length := by cases b <;> simpa using ha
      simp only [List.length_cons]
      omega
    · have hh := ih ha
      simp only [List.length_cons]
      omega

theorem oneIndices_pairwise (w : List Bool) : (oneIndices w).Pairwise (fun a b => b < a) := by
  induction w with
  | nil => simp [oneIndices]
  | cons b w ih =>
    cases b with
    | false => simpa [oneIndices] using ih
    | true =>
      simp only [oneIndices, if_true, List.singleton_append, List.pairwise_cons]
      exact ⟨fun a ha => oneIndices_mem_lt w a ha, ih⟩

/-- Index membership recovers each source bit, including every zero between
consecutive retained indices. -/
theorem oneIndices_mem_iff (w : List Bool) (a : Nat) :
    a ∈ oneIndices w ↔ a < w.length ∧ w[w.length-1-a]? = some true := by
  induction w with
  | nil => simp [oneIndices]
  | cons b w ih =>
    by_cases he : a = w.length
    · subst a
      have hn : w.length ∉ oneIndices w := by intro hm; have := oneIndices_mem_lt w _ hm; omega
      cases b <;> simp [oneIndices, hn]
    · by_cases ha : a < w.length
      · have hp : (b::w).length-1-a = (w.length-1-a)+1 := by simp only [List.length_cons]; omega
        rw [hp, List.getElem?_cons_succ]
        cases b <;> simp [oneIndices, ih, he, ha, Nat.lt_succ_of_lt ha]
      · have hn : a ∉ oneIndices w := by intro hm; have := oneIndices_mem_lt w _ hm; omega
        have hle : ¬ a < w.length+1 := by omega
        cases b <;> simp [oneIndices, hn, he, hle]

/-- A consecutive segment of a strictly decreasing list contains every
ambient-list index lying between two of the segment's own indices. -/
theorem decreasing_infix_mem_iff (w v : List Nat)
    (hw : w.Pairwise (fun a b => b < a)) (hv : v.IsInfix w)
    (lo hi : Nat) (hlo : lo ∈ v) (hhi : hi ∈ v) (a : Nat)
    (hal : lo ≤ a) (hah : a ≤ hi) : a ∈ w ↔ a ∈ v := by
  constructor
  · intro ha
    obtain ⟨pre, post, rfl⟩ := hv
    have hpw := List.pairwise_append.mp hw
    have hpv := List.pairwise_append.mp hpw.1
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · have hh := hpv.2.2 a ha hi hhi
        omega
      · exact ha
    · have hh := hpw.2.2 lo (List.mem_append_right _ hlo) a ha
      omega
  · exact fun ha => hv.subset ha

/-- Equal consecutive primary-index factors determine the full binary
interval between any two of their indices. This is the reconstruction step
used in equation (22), with both positive and zero bits accounted for. -/
theorem equal_index_factors_reconstruct (w z : List Bool) (v : List Nat)
    (hw : v.IsInfix (oneIndices w)) (hz : v.IsInfix (oneIndices z))
    (lo hi : Nat) (hlo : lo ∈ v) (hhi : hi ∈ v) (hlh : lo ≤ hi) :
    ∀ k, k < hi+1-lo →
      w[w.length-1-hi+k]? = z[z.length-1-hi+k]? := by
  have hiw := oneIndices_mem_lt w hi (hw.subset hhi)
  have hiz := oneIndices_mem_lt z hi (hz.subset hhi)
  intro k hk
  let a := hi-k
  have hal : lo ≤ a := by dsimp [a]; omega
  have hah : a ≤ hi := by dsimp [a]; omega
  have hawmem := decreasing_infix_mem_iff (oneIndices w) v (oneIndices_pairwise w) hw lo hi hlo hhi a hal hah
  have hazmem := decreasing_infix_mem_iff (oneIndices z) v (oneIndices_pairwise z) hz lo hi hlo hhi a hal hah
  have hmem : a ∈ oneIndices w ↔ a ∈ oneIndices z := hawmem.trans hazmem.symm
  rw [oneIndices_mem_iff, oneIndices_mem_iff] at hmem
  have haw : a < w.length := by omega
  have haz : a < z.length := by omega
  simp only [haw, haz, true_and] at hmem
  have hew : w.length-1-a = w.length-1-hi+k := by dsimp [a]; omega
  have hez : z.length-1-a = z.length-1-hi+k := by dsimp [a]; omega
  rw [hew, hez] at hmem
  have hbw : w.length-1-hi+k < w.length := by omega
  have hbz : z.length-1-hi+k < z.length := by omega
  rw [List.getElem?_eq_getElem hbw, List.getElem?_eq_getElem hbz] at hmem ⊢
  cases hwe : w[w.length-1-hi+k] <;> cases hze : z[z.length-1-hi+k] <;> simp_all

end GreedyLowerBound
