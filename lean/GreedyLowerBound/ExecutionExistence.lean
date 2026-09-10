import GreedyLowerBound.InitialGrammar
import GreedyLowerBound.MaximalFactors
import Mathlib.Data.List.Sublists
import Mathlib.Data.Finset.Max

set_option autoImplicit false
namespace GreedyLowerBound
namespace Grammar

/-- A finite superset of the eligible factors. Sublists are used only to
prove finiteness; eligibility still requires actual disjoint occurrences. -/
noncomputable def eligibleCandidates (G : Grammar) : Finset (Word Nat) := by
  classical
  exact (G.defined.biUnion (fun i => (G.rhs i).sublists.toFinset)).filter G.Eligible

theorem mem_eligibleCandidates (G : Grammar) (v : Word Nat) :
    v ∈ G.eligibleCandidates ↔ G.Eligible v := by
  classical
  constructor
  · exact fun hv => (Finset.mem_filter.mp hv).2
  · intro hv
    have hvn : v ≠ [] := by intro he; have hh := hv.1; simp [he] at hh
    obtain ⟨i, hi, hc⟩ : ∃ i ∈ G.defined, 0 < scanCount v (G.rhs i) := by
      by_contra hn
      have hz : G.frequency v = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        by_contra hz
        exact hn ⟨i, hi, by omega⟩
      have hh := hv.2
      omega
    have hin := (scanCount_is_maximum v (G.rhs i) hvn).1.factor_isInfix hc
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_biUnion.mpr ⟨i, hi,
      List.mem_toFinset.mpr (List.mem_sublists.mpr hin.sublist)⟩, hv⟩

/-- Every nonterminal algorithm state has a factor attaining the global
maximum gain. This supplies existence independently of tie resolution. -/
theorem maximizing_factor_exists (G : Grammar) (hG : ¬ G.Terminal) :
    ∃ v, G.Eligible v ∧ ∀ u, G.Eligible u → G.gain u ≤ G.gain v := by
  classical
  have hn : G.eligibleCandidates.Nonempty := by
    by_contra he
    apply hG
    intro v hv
    exact he ⟨v, (G.mem_eligibleCandidates v).mpr hv⟩
  obtain ⟨v, hv, hm⟩ := Finset.exists_max_image G.eligibleCandidates G.gain hn
  exact ⟨v, (G.mem_eligibleCandidates v).mp hv,
    fun u hu => hm u ((G.mem_eligibleCandidates u).mpr hu)⟩

/-- Fresh names and the simultaneous scans always define a global step. -/
theorem globalStep_exists (G : Grammar) (v : Word Nat) (hv : v ≠ []) :
    ∃ H fresh, GlobalStep G H v fresh (fun i => scanCount v (G.rhs i)) := by
  classical
  let used := G.defined ∪ {G.start} ∪ v.toFinset ∪
    G.defined.biUnion (fun i => (G.rhs i).toFinset)
  let fresh := used.sup id + 1
  have hf : fresh ∉ used := by
    intro hm
    have hl : fresh ≤ used.sup id := Finset.le_sup (f := id) hm
    dsimp [fresh] at hl
    omega
  have hfd : fresh ∉ G.defined := by
    intro hm
    exact hf (by simp [used, hm])
  have hfs : fresh ≠ G.start := by
    intro he
    exact hf (by simp [used, he])
  have hfv : fresh ∉ v := by
    intro hm
    exact hf (by simp [used, hm])
  have hfr : ∀ i ∈ G.defined, fresh ∉ G.rhs i := by
    intro i hi hm
    apply hf
    have hb : fresh ∈ G.defined.biUnion (fun j => (G.rhs j).toFinset) :=
      Finset.mem_biUnion.mpr ⟨i, hi, List.mem_toFinset.mpr hm⟩
    exact Finset.mem_union_right _ hb
  let H : Grammar := ⟨insert fresh G.defined,
    fun i => if i = fresh then v else scanOutput v fresh (G.rhs i), G.start⟩
  refine ⟨H, fresh, hfd, hfs, hfr, hfv, rfl, rfl, ?_, ?_⟩
  · simp [H]
  · intro i hi
    have hn : i ≠ fresh := by intro he; subst i; exact hfd hi
    simpa only [H, if_neg hn] using scanOutput_spec v fresh (G.rhs i) hv

theorem greedyStep_exists (G : Grammar) (hG : ¬ G.Terminal) : ∃ H, GreedyStep G H := by
  obtain ⟨v, hv, hm⟩ := G.maximizing_factor_exists hG
  have hvn : v ≠ [] := by intro he; have hh := hv.1; simp [he] at hh
  obtain ⟨H, fresh, hr⟩ := G.globalStep_exists v hvn
  exact ⟨H, v, fresh, hr, hv, hm⟩

/-- Every well-formed grammar admits a complete Greedy execution, including
zero-gain rounds. The decreasing measure is size minus number of rules. -/
theorem terminal_run_exists (G : Grammar) (hG : G.WellFormed) :
    ∃ H n, GreedyRun G H n ∧ H.Terminal := by
  have aux : ∀ k G, G.size-G.defined.card = k → G.WellFormed →
      ∃ H n, GreedyRun G H n ∧ H.Terminal := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro G hk hG
      by_cases ht : G.Terminal
      · exact ⟨G, 0, GreedyRun.nil G, ht⟩
      · obtain ⟨H, hs⟩ := G.greedyStep_exists ht
        have hH := hs.wellFormed hG
        have hl := H.card_le_size hH
        have hc := hs.card_eq
        have hz := hs.size_le
        have hlt : H.size-H.defined.card < k := by omega
        obtain ⟨K, n, hr, ht⟩ := ih (H.size-H.defined.card) hlt H rfl hH
        exact ⟨K, n+1, GreedyRun.cons hs hr, ht⟩
  exact aux (G.size-G.defined.card) G rfl hG

end Grammar
end GreedyLowerBound
