import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace GreedyLowerBound
namespace Directed

variable {E V : Type}

/-- An edge-labelled directed walk, preserving parallel edges and loops. -/
inductive Walk (src dst : E → V) : V → List E → V → Prop
  | nil (v : V) : Walk src dst v [] v
  | cons (e : E) {es : List E} {v : V} :
      Walk src dst (dst e) es v → Walk src dst (src e) (e::es) v

variable {src dst : E → V}

theorem Walk.append {x y z : V} {es fs : List E}
    (he : Walk src dst x es y) (hf : Walk src dst y fs z) :
    Walk src dst x (es++fs) z := by
  induction he with
  | nil => exact hf
  | cons e he ih => exact Walk.cons e (ih hf)

theorem Walk.start_mem {x y : V} {es : List E} (h : Walk src dst x es y) :
    x ∈ y :: es.map src := by
  cases h with
  | nil => simp
  | cons e h => simp

theorem Walk.destination_mem {x y : V} {es : List E} (h : Walk src dst x es y)
    (e : E) (he : e ∈ es) : dst e ∈ y :: es.map src := by
  induction h with
  | nil => simp at he
  | cons a h ih =>
    rcases List.mem_cons.mp he with rfl | he
    · have hm := h.start_mem
      simp only [List.map_cons, List.mem_cons] at hm ⊢
      tauto
    · have hm := ih he
      simp only [List.map_cons, List.mem_cons] at hm ⊢
      tauto

/-- Split a walk at any vertex encountered before an edge, including its start. -/
theorem Walk.split_at_vertex {x y v : V} {es : List E} (h : Walk src dst x es y)
    (hv : v ∈ x :: es.map src) :
    ∃ pre post, es = pre++post ∧ Walk src dst x pre v ∧ Walk src dst v post y := by
  induction h with
  | nil x =>
    have he : v = x := by simpa using hv
    subst v
    exact ⟨[], [], rfl, Walk.nil x, Walk.nil x⟩
  | @cons e es y ht ih =>
    by_cases he : v = src e
    · subst v
      exact ⟨[], e::_, rfl, Walk.nil _, Walk.cons e ht⟩
    · have hm : v ∈ dst e :: es.map src := by
        have hm : v ∈ es.map src := by simpa only [List.map_cons, List.mem_cons, he, false_or] using hv
        exact List.mem_cons_of_mem _ hm
      obtain ⟨pre, post, hr, hpre, hpost⟩ := ih hm
      exact ⟨e::pre, post, by rw [hr]; rfl, Walk.cons e hpre, hpost⟩

theorem Walk.first_source {x y : V} {es : List E} (h : Walk src dst x es y)
    (ha : 0 < es.length) : src (es[0]'ha) = x := by
  cases h with
  | nil => simp at ha
  | cons e ht => rfl

/-- Consecutive edges of a walk meet at the same vertex. -/
theorem Walk.adjacent {x y : V} {es : List E} (h : Walk src dst x es y)
    (a : Nat) (ha : a+1 < es.length) :
    dst (es[a]'(by omega)) = src (es[a+1]'ha) := by
  induction h generalizing a with
  | nil => simp at ha
  | @cons e es y ht ih =>
    cases a with
    | zero =>
      simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
        (ht.first_source (by simpa using ha)).symm
    | succ a =>
      simpa only [List.getElem_cons_succ] using ih a (by simpa using ha)

variable [DecidableEq E] [DecidableEq V]

def outDegree (src : E → V) (R : Finset E) (v : V) : Nat := ∑ e ∈ R, if src e = v then 1 else 0
def inDegree (dst : E → V) (R : Finset E) (v : V) : Nat := ∑ e ∈ R, if dst e = v then 1 else 0

def Balanced (src dst : E → V) (R : Finset E) : Prop :=
  ∀ v, outDegree src R v = inDegree dst R v

/-- The remaining degrees after a walk from s to x. -/
def Defect (src dst : E → V) (R : Finset E) (s x : V) : Prop :=
  ∀ v, outDegree src R v + (if s = v then 1 else 0) =
    inDegree dst R v + (if x = v then 1 else 0)

theorem balanced_defect (R : Finset E) (hR : Balanced src dst R) (s : V) : Defect src dst R s s := by
  intro v
  rw [hR v]

theorem defect_closed (R : Finset E) (s : V) (hR : Defect src dst R s s) : Balanced src dst R := by
  intro v
  exact Nat.add_right_cancel (hR v)

theorem defect_has_outgoing (R : Finset E) (s x : V) (hR : Defect src dst R s x) (hne : x ≠ s) :
    ∃ e ∈ R, src e = x := by
  by_contra hn
  have hz : outDegree src R x = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have hh : src e ≠ x := fun hx => hn ⟨e, he, hx⟩
    simp only [if_neg hh]
  have hh := hR x
  rw [hz, if_neg (Ne.symm hne), if_pos rfl] at hh
  omega

theorem defect_erase (R : Finset E) (s x : V) (hR : Defect src dst R s x)
    (e : E) (he : e ∈ R) (hx : src e = x) : Defect src dst (R.erase e) s (dst e) := by
  intro v
  have ho : outDegree src (R.erase e) v + (if src e = v then 1 else 0) = outDegree src R v :=
    Finset.sum_erase_add _ _ he
  have hi : inDegree dst (R.erase e) v + (if dst e = v then 1 else 0) = inDegree dst R v :=
    Finset.sum_erase_add _ _ he
  have hh := hR v
  rw [hx] at ho
  omega

/-- Following unused outgoing edges must close at the required start.
The recursion is on the finite remaining edge set, not on a presumed tour. -/
theorem close_walk (R : Finset E) (s x : V) (hR : Defect src dst R s x) :
    ∃ es, Walk src dst x es s ∧ es.Nodup ∧ (∀ e ∈ es, e ∈ R) ∧
      Balanced src dst (R \ es.toFinset) := by
  have aux : ∀ n R, R.card = n → ∀ s x, Defect src dst R s x →
      ∃ es, Walk src dst x es s ∧ es.Nodup ∧ (∀ e ∈ es, e ∈ R) ∧
        Balanced src dst (R \ es.toFinset) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro R hn s x hR
      by_cases he : x = s
      · subst x
        exact ⟨[], Walk.nil s, by simp, by simp, by simpa using defect_closed R s hR⟩
      · obtain ⟨e, he, hx⟩ := defect_has_outgoing R s x hR he
        have hcard : (R.erase e).card < n := by rw [← hn]; exact Finset.card_erase_lt_of_mem he
        obtain ⟨es, hw, hd, hs, hb⟩ := ih (R.erase e).card hcard (R.erase e) rfl s (dst e)
          (defect_erase R s x hR e he hx)
        have hen : e ∉ es := by intro hm; exact (Finset.mem_erase.mp (hs e hm)).1 rfl
        refine ⟨e::es, hx ▸ Walk.cons e hw, List.nodup_cons.mpr ⟨hen, hd⟩, ?_, ?_⟩
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact he
          · exact (Finset.mem_erase.mp (hs a ha)).2
        · have heq : R \ (e::es).toFinset = R.erase e \ es.toFinset := by
            ext a
            simp [and_assoc, and_left_comm, and_comm]
          rwa [heq]
  exact aux R.card R rfl s x hR

/-- A balanced remainder with an outgoing edge at v contains a nonempty
closed trail at v and still has a balanced remainder afterwards. -/
theorem nonempty_closed_trail (R : Finset E) (hR : Balanced src dst R)
    (e : E) (he : e ∈ R) :
    ∃ es, Walk src dst (src e) es (src e) ∧ es.Nodup ∧ es ≠ [] ∧
      (∀ a ∈ es, a ∈ R) ∧ Balanced src dst (R \ es.toFinset) := by
  obtain ⟨es, hw, hd, hs, hb⟩ := close_walk (R.erase e) (src e) (dst e)
    (defect_erase R (src e) (src e) (balanced_defect R hR (src e)) e he rfl)
  have hen : e ∉ es := by intro hm; exact (Finset.mem_erase.mp (hs e hm)).1 rfl
  refine ⟨e::es, Walk.cons e hw, List.nodup_cons.mpr ⟨hen, hd⟩, by simp, ?_, ?_⟩
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact he
    · exact (Finset.mem_erase.mp (hs a ha)).2
  · have heq : R \ (e::es).toFinset = R.erase e \ es.toFinset := by
      ext a
      simp [and_assoc, and_left_comm, and_comm]
    rwa [heq]

/-- Reachability preserves any set closed under the available edges. -/
theorem Walk.mem_of_closed {R : Finset E} {S : Set V}
    (hclosed : ∀ e ∈ R, src e ∈ S → dst e ∈ S)
    {x y : V} {es : List E} (hw : Walk src dst x es y)
    (hs : ∀ e ∈ es, e ∈ R) (hx : x ∈ S) : y ∈ S := by
  induction hw with
  | nil => exact hx
  | cons e hw ih =>
    apply ih (fun a ha => hs a (List.mem_cons_of_mem e ha))
    exact hclosed e (hs e (by simp)) hx

/-- Directed connectivity uses the actual finite edge set. -/
def Connected (src dst : E → V) (R : Finset E) : Prop :=
  ∀ x y, ∃ es, Walk src dst x es y ∧ ∀ e ∈ es, e ∈ R

theorem unused_edge_at_visited (R : Finset E) (hc : Connected src dst R)
    (s : V) (es : List E) (hw : Walk src dst s es s)
    (hr : (R \ es.toFinset).Nonempty) :
    ∃ e ∈ R \ es.toFinset, src e ∈ s :: es.map src := by
  by_contra hn
  have hclosed : ∀ e ∈ R, src e ∈ s :: es.map src → dst e ∈ s :: es.map src := by
    intro e he hv
    have hem : e ∈ es := by
      by_contra hem
      exact hn ⟨e, Finset.mem_sdiff.mpr ⟨he, by simpa using hem⟩, hv⟩
    exact hw.destination_mem e hem
  obtain ⟨e, he⟩ := hr
  obtain ⟨path, hp, hs⟩ := hc s (src e)
  have hv := hp.mem_of_closed (S := {v | v ∈ s :: es.map src}) hclosed hs (by simp : s ∈ s :: es.map src)
  exact hn ⟨e, he, hv⟩

/-- A connected balanced finite directed multigraph has an Eulerian circuit.
Loops and parallel edges are retained as distinct edge labels. -/
theorem eulerian_circuit (R : Finset E) (hb : Balanced src dst R)
    (hc : Connected src dst R) (s : V) :
    ∃ es, Walk src dst s es s ∧ es.Nodup ∧ es.toFinset = R := by
  have aux : ∀ n es, (R \ es.toFinset).card = n →
      Walk src dst s es s → es.Nodup → (∀ e ∈ es, e ∈ R) →
      Balanced src dst (R \ es.toFinset) →
      ∃ fs, Walk src dst s fs s ∧ fs.Nodup ∧ fs.toFinset = R := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro es hn hw hd hs hb
      by_cases hz : R \ es.toFinset = ∅
      · refine ⟨es, hw, hd, Finset.Subset.antisymm ?_ ?_⟩
        · intro e he
          exact hs e (by simpa using he)
        · exact Finset.sdiff_eq_empty_iff_subset.mp hz
      · have hr : (R \ es.toFinset).Nonempty := Finset.nonempty_iff_ne_empty.mpr hz
        obtain ⟨e, he, hv⟩ := unused_edge_at_visited R hc s es hw hr
        obtain ⟨pre, post, hep, hpre, hpost⟩ := hw.split_at_vertex hv
        obtain ⟨cycle, hcycle, hcd, hcne, hcs, hcb⟩ := nonempty_closed_trail _ hb e he
        have hdis : ∀ a ∈ cycle, a ∉ es := by
          intro a ha
          exact fun hm => (Finset.mem_sdiff.mp (hcs a ha)).2 (by simpa using hm)
        have hnd : (pre ++ cycle ++ post).Nodup := by
          rw [hep, List.nodup_append] at hd
          simp only [List.nodup_append, List.disjoint_left, List.mem_append]
          rcases hd with ⟨hpd, hod, hpo⟩
          refine ⟨⟨hpd, hcd, ?_⟩, hod, ?_⟩
          · intro a hap hac
            exact hdis a hac (by rw [hep]; exact List.mem_append_left _ hap)
          · intro a ha hao
            rcases ha with hap | hac
            · exact List.disjoint_left.mp hpo hap hao
            · exact hdis a hac (by rw [hep]; exact List.mem_append_right _ hao)
        have hsub : ∀ a ∈ pre ++ cycle ++ post, a ∈ R := by
          intro a ha
          simp only [List.mem_append] at ha
          rcases ha with (hap | hac) | hao
          · exact hs a (by rw [hep]; exact List.mem_append_left _ hap)
          · exact (Finset.mem_sdiff.mp (hcs a hac)).1
          · exact hs a (by rw [hep]; exact List.mem_append_right _ hao)
        have hrem : R \ (pre ++ cycle ++ post).toFinset =
            (R \ es.toFinset) \ cycle.toFinset := by
          rw [hep]
          ext a
          simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_append]
          tauto
        have hlt : (R \ (pre ++ cycle ++ post).toFinset).card < n := by
          rw [hrem, ← hn]
          apply Finset.card_lt_card
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨Finset.sdiff_subset, ?_⟩
          intro heq
          obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil cycle hcne
          have har := hcs a ha
          have ham : a ∈ (R \ es.toFinset) \ cycle.toFinset := by rw [heq]; exact har
          exact (Finset.mem_sdiff.mp ham).2 (by simpa using ha)
        exact ih _ hlt _ rfl ((hpre.append hcycle).append hpost) hnd hsub (hrem ▸ hcb)
  exact aux (R \ ([] : List E).toFinset).card [] rfl (Walk.nil s)
    (by simp) (by simp) (by simpa using hb)

end Directed
end GreedyLowerBound
