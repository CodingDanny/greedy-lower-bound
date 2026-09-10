import GreedyLowerBound.BinaryOverlapGraph
import GreedyLowerBound.BinaryWindows

set_option autoImplicit false
namespace GreedyLowerBound
namespace BinaryOverlap

/-- Overlap propagates each letter of an edge to the first letter of a later
edge. The bound excludes wrapping around the cut in the finite tour. -/
theorem walk_bit_at_distance (m : Nat) {x y : Vertex m} {es : List (Edge m)}
    (hw : Directed.Walk (source m) (target m) x es y)
    (a k : Nat) (ha : a+k < es.length) (hk : k < m+1) :
    (es[a]'(by omega)) ⟨k,hk⟩ = (es[a+k]'ha) 0 := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    have had : a+1 < es.length := by omega
    have he := congrArg (fun v : Vertex m => v ⟨k, by omega⟩) (hw.adjacent a had)
    change (es[a]'(by omega)) ⟨k+1,hk⟩ = (es[a+1]'had) ⟨k,by omega⟩ at he
    rw [he]
    have hh := ih (a+1) (by omega) (by omega)
    have hi : (⟨a+1+k, by omega⟩ : Fin es.length) = ⟨a+(k+1),ha⟩ := by
      apply Fin.ext
      change a+1+k = a+(k+1)
      omega
    exact hh.trans (congrArg (fun j : Fin es.length => (es[j.val]'j.isLt) 0) hi)

/-- Read the initial bit of each edge. Any complete window recovers the
entire corresponding edge, so an edge-simple tour has unique windows. -/
theorem tour_unique_windows (m : Nat) {x y : Vertex m} {es : List (Edge m)}
    (hw : Directed.Walk (source m) (target m) x es y) (hd : es.Nodup) :
    UniqueWindows (es.map (fun e => e 0)) (m+1) := by
  intro a b ha hb he
  simp only [List.length_map] at ha hb
  have ha' : a < es.length := by omega
  have hb' : b < es.length := by omega
  apply hd.getElem_inj_iff.mp (show es[a] = es[b] from ?_)
  funext i
  have haik : a+i.val < es.length := by omega
  have hbik : b+i.val < es.length := by omega
  have hh := he i.val i.isLt
  change (es.map (fun e => e 0))[a+i.val]? = (es.map (fun e => e 0))[b+i.val]? at hh
  rw [List.getElem?_eq_getElem (by simpa using haik),
    List.getElem?_eq_getElem (by simpa using hbik),
    List.getElem_map, List.getElem_map, Option.some.injEq] at hh
  exact (walk_bit_at_distance m hw a i.val haik i.isLt).trans
    (hh.trans (walk_bit_at_distance m hw b i.val hbik i.isLt).symm)

end BinaryOverlap

/-- A binary seed of de Bruijn length exists, with every linear q-window
occurring at most once. No combinatorial existence statement is assumed. -/
theorem unique_binary_seed_exists (q : Nat) (hq : 0 < q) :
    ∃ D : List Bool, D.length = 2^q ∧ UniqueWindows D q := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  obtain ⟨es, hw, hd, hs, hl⟩ := BinaryOverlap.edge_tour_exists m
  exact ⟨es.map (fun e => e 0), by simpa using hl,
    BinaryOverlap.tour_unique_windows m hw hd⟩

/-- The exact seed parameters used by the lower-bound construction. -/
theorem lower_bound_seed_exists (r : Nat) (hr : 1 ≤ r) :
    ∃ D : List Bool, D.length = (2^r)^2 ∧ UniqueWindows D (2*r) := by
  obtain ⟨D, hD, hu⟩ := unique_binary_seed_exists (2*r) (by omega)
  refine ⟨D, ?_, hu⟩
  rw [hD, ← Nat.pow_mul]
  congr 1
  omega

end GreedyLowerBound
