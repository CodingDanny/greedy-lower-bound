import GreedyLowerBound.Cleanup

set_option autoImplicit false

namespace GreedyLowerBound

/-- Canonical scan output, defined by the already proved existence theorem.
The empty-factor branch is immaterial to eligible substitutions. -/
noncomputable def scanOutput (v : Word Nat) (fresh : Nat) (w : Word Nat) : Word Nat :=
  if hv : v = [] then w else Classical.choose (Scan.exists_output v w fresh hv)

theorem scanOutput_spec (v : Word Nat) (fresh : Nat) (w : Word Nat) (hv : v ≠ []) :
    Scan v fresh w (scanOutput v fresh w) (scanCount v w) := by
  simpa only [scanOutput, dif_neg hv] using
    Classical.choose_spec (Scan.exists_output v w fresh hv)

theorem Scan.output_eq {v s t : Word Nat} {fresh c : Nat}
    (h : Scan v fresh s t c) (hv : v ≠ []) : t = scanOutput v fresh s :=
  h.output_unique (scanOutput_spec v fresh s hv) hv

namespace Fragmentation

/-- A complete global substitution preserves the literal fragment boundaries.
No special restrictions on the selected factor beyond eligibility are used. -/
noncomputable def afterStep {G H : Grammar} (P : Fragmentation G)
    {v : Word Nat} {fresh : Nat} {counts : Nat → Nat}
    (hr : GlobalStep G H v fresh counts) (hv : G.Eligible v) : Fragmentation H := by
  have hvn : v ≠ [] := by intro he; have hh := hv.1; simp [he] at hh
  refine {
    first := scanOutput v fresh P.first
    rest := P.rest.map (fun p => (p.1, scanOutput v fresh p.2))
    start_mem := ?_
    start_eq := ?_
    separators := ?_ }
  · rw [hr.domain, hr.start]
    exact Finset.mem_insert_of_mem P.start_mem
  · rw [hr.start]
    have hz : ∀ p ∈ P.rest, p.1 ∉ v := by
      intro p hp
      exact G.eligible_excludes_single_symbol v p.1 hv
        (by rw [(P.separators p hp).symbolCount])
    have hs := (scanOutput_spec v fresh P.first hvn).joinFragments P.rest
      (fun p => scanOutput v fresh p.2) hvn hz
      (fun p _ => scanOutput_spec v fresh p.2 hvn)
    rw [← P.start_eq] at hs
    exact (hr.scans G.start P.start_mem).output_unique hs hvn
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hr.preserves_separator hv (P.separators q hq)

theorem afterStep_first {G H : Grammar} (P : Fragmentation G)
    {v : Word Nat} {fresh : Nat} {counts : Nat → Nat}
    (hr : GlobalStep G H v fresh counts) (hv : G.Eligible v) :
    (P.afterStep hr hv).first = scanOutput v fresh P.first := rfl

theorem afterStep_rest {G H : Grammar} (P : Fragmentation G)
    {v : Word Nat} {fresh : Nat} {counts : Nat → Nat}
    (hr : GlobalStep G H v fresh counts) (hv : G.Eligible v) :
    (P.afterStep hr hv).rest = P.rest.map (fun p => (p.1, scanOutput v fresh p.2)) := rfl

/-- Every new storage cell is accounted for: scan every old cell and add the
fresh definition once. The arbitrary enumeration of nonterminals is handled
by permutation, without imposing an order on symbol names. -/
theorem afterStep_pieces {G H : Grammar} (P : Fragmentation G)
    {v : Word Nat} {fresh : Nat} {counts : Nat → Nat}
    (hr : GlobalStep G H v fresh counts) (hv : G.Eligible v) :
    (P.afterStep hr hv).pieces.Perm (P.pieces.map (scanOutput v fresh) ++ [v]) := by
  have hvn : v ≠ [] := by intro he; have hh := hv.1; simp [he] at hh
  have hdom : H.defined.erase H.start = insert fresh (G.defined.erase G.start) := by
    rw [hr.domain, hr.start, Finset.erase_insert_of_ne hr.fresh_start]
  have hf : fresh ∉ G.defined.erase G.start := by
    intro hm
    exact hr.fresh_defined (Finset.mem_erase.mp hm).2
  have hp := (Finset.toList_insert hf).map H.rhs
  rw [List.map_cons, hr.new_rule] at hp
  have he : (G.defined.erase G.start).toList.map H.rhs =
      ((G.defined.erase G.start).toList.map G.rhs).map (scanOutput v fresh) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact (hr.scans i (Finset.mem_erase.mp (Finset.mem_toList.mp hi)).2).output_eq hvn
  rw [he] at hp
  unfold pieces
  rw [afterStep_first, afterStep_rest, hdom]
  simp only [List.map_append, List.map_cons, List.map_map, Function.comp_def]
  have hp' := hp.append_left
    (scanOutput v fresh P.first :: P.rest.map (fun p => scanOutput v fresh p.2))
  exact hp'.trans (by
    simpa only [List.singleton_append, List.append_assoc, List.map_map, Function.comp_def] using
      (List.perm_append_comm (l₁ := [v])
        (l₂ := ((G.defined.erase G.start).toList.map G.rhs).map (scanOutput v fresh))).append_left
          (scanOutput v fresh P.first :: P.rest.map (fun p => scanOutput v fresh p.2)))

end Fragmentation

end GreedyLowerBound
