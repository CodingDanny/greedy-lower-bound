import GreedyLowerBound.MaximumOccurrences
import GreedyLowerBound.SpacingEstimates

set_option autoImplicit false

namespace GreedyLowerBound

theorem prefix_drop_get {α : Type} (v w : Word α) (p : Nat)
    (hp : v.IsPrefix (w.drop p)) (k : Nat) (hk : k < v.length) :
    w[p+k]? = v[k]? := by
  obtain ⟨rest, he⟩ := hp
  calc
    w[p+k]? = (w.drop p)[k]? := List.getElem?_drop.symm
    _ = (v++rest)[k]? := congrArg (fun s : Word α => s[k]?) he.symm
    _ = v[k]? := List.getElem?_append_left hk

/-- A disjoint packing in a power-free word satisfies the stronger spacing
bound, including the unused prefix before its first occurrence. -/
theorem Packing.first_span {α : Type} (v : Word α) (hv : v ≠ []) (c : Nat)
    (w : Word α) (h : Packing v w (c+1)) (hg : PowerFree w) :
    ∃ p, v.IsPrefix (w.drop p) ∧
      3*p + 4*v.length*c + 3*v.length ≤ 3*w.length := by
  induction c generalizing w with
  | zero =>
    cases h with
    | next pre rest ht =>
      refine ⟨pre.length, ?_, ?_⟩
      · rw [List.drop_left]
        exact List.prefix_append v rest
      · simp only [Nat.mul_zero, Nat.add_zero, List.length_append]
        omega
  | succ c ih =>
    cases h with
    | next pre rest ht =>
      have hgr : PowerFree rest := by
        have hh := hg.drop (pre++v).length
        simpa only [← List.append_assoc, List.drop_left] using hh
      obtain ⟨q, hq, hspan⟩ := ih rest ht hgr
      have hp : v.IsPrefix ((pre++(v++rest)).drop pre.length) := by
        rw [List.drop_left]
        exact List.prefix_append v rest
      have hpq : v.IsPrefix ((pre++(v++rest)).drop (pre.length+(v.length+q))) := by
        rw [List.drop_append, List.drop_append]
        exact hq
      have hvpos := List.length_pos_iff.mpr hv
      have hb : pre.length+(v.length+q)+v.length ≤ (pre++(v++rest)).length := by
        simp only [List.length_append]
        omega
      have he : EqualIntervals (pre++(v++rest)) pre.length (pre.length+(v.length+q)) v.length := by
        intro k hk
        exact (prefix_drop_get v _ _ hp k hk).trans (prefix_drop_get v _ _ hpq k hk).symm
      have hs := occurrence_spacing _ hg pre.length (v.length+q) v.length hb (by omega) he
      refine ⟨pre.length, hp, ?_⟩
      rw [Nat.mul_succ]
      simp only [List.length_append]
      omega

theorem Packing.spacing {α : Type} (v w : Word α) (c : Nat)
    (h : Packing v w c) (hv : v ≠ []) (hc : 0 < c) (hg : PowerFree w) :
    4*v.length*(c-1)+3*v.length ≤ 3*w.length := by
  have he : c-1+1 = c := by omega
  have h' : Packing v w ((c-1)+1) := by simpa only [he] using h
  obtain ⟨p, _, hs⟩ := h'.first_span v hv (c-1) w hg
  omega

end GreedyLowerBound
