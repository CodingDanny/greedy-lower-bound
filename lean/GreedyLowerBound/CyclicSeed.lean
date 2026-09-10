import GreedyLowerBound.SeedExistence

set_option autoImplicit false
namespace GreedyLowerBound

/-- Reading a doubled finite word realizes one wrap around its cyclic cut. -/
theorem doubled_get_mod {α : Type} (w : List α) (k : Nat) (hk : k < 2*w.length) :
    (w++w)[k]? = w[k%w.length]? := by
  by_cases h : k < w.length
  · rw [List.getElem?_append_left h, Nat.mod_eq_of_lt h]
  · rw [List.getElem?_append_right (by omega), Nat.mod_eq_sub_mod (by omega),
      Nat.mod_eq_of_lt (by omega)]

namespace BinaryOverlap

theorem tour_cyclic_window (m : Nat) {x : Vertex m} {es : List (Edge m)}
    (hw : Directed.Walk (source m) (target m) x es x)
    (hl : m+1 ≤ es.length) (a k : Nat) (ha : a < es.length) (hk : k < m+1) :
    (es.map (fun e => e 0))[(a+k)%es.length]? = some ((es[a]'ha) ⟨k,hk⟩) := by
  have hab : a+k < (es++es).length := by simp only [List.length_append]; omega
  have he := walk_bit_at_distance m (hw.append hw) a k hab hk
  rw [List.getElem_append_left ha] at he
  have hh : ((es++es).map (fun e => e 0))[a+k]? = some ((es[a]'ha) ⟨k,hk⟩) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hab]
    exact congrArg some he.symm
  rw [List.map_append, doubled_get_mod _ (a+k) (by simp only [List.length_map]; omega)] at hh
  simpa only [List.length_map] using hh

end BinaryOverlap

/-- Every binary q-word occurs at exactly one cyclic starting position. -/
def CyclicDeBruijn (D : List Bool) (q : Nat) : Prop :=
  D.length = 2^q ∧ ∀ v : Fin q → Bool, ∃! a : Fin D.length,
    ∀ k : Fin q, D[(a.val+k.val)%D.length]? = some (v k)

/-- The full cyclic de Bruijn existence statement, beyond the linear
uniqueness property sufficient for the lower bound. -/
theorem cyclic_deBruijn_exists (q : Nat) (hq : 0 < q) :
    ∃ D : List Bool, CyclicDeBruijn D q := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  obtain ⟨es, hw, hd, hs, hl⟩ := BinaryOverlap.edge_tour_exists m
  have hq : m+1 ≤ es.length := by rw [hl]; exact Nat.le_of_lt Nat.lt_two_pow_self
  refine ⟨es.map (fun e => e 0), by simpa using hl, ?_⟩
  intro v
  have hv : v ∈ es := by
    apply List.mem_toFinset.mp
    rw [hs]
    exact Finset.mem_univ _
  obtain ⟨a, ha, he⟩ := List.getElem_of_mem hv
  refine ⟨⟨a, by simpa using ha⟩, ?_, ?_⟩
  · intro k
    simpa only [List.length_map, he] using BinaryOverlap.tour_cyclic_window m hw hq a k.val ha k.isLt
  · intro b hb
    apply Fin.ext
    have hbe : b.val < es.length := by simpa using b.isLt
    apply hd.getElem_inj_iff.mp (show es[b.val] = es[a] from ?_)
    funext k
    have hh := hb k
    simp only [List.length_map] at hh
    rw [BinaryOverlap.tour_cyclic_window m hw hq b.val k.val hbe k.isLt,
      Option.some.injEq] at hh
    exact hh.trans (congrArg (fun e => e k) he).symm

theorem CyclicDeBruijn.uniqueWindows (D : List Bool) (q : Nat) (hq : 0 < q)
    (hD : CyclicDeBruijn D q) : UniqueWindows D q := by
  intro a b ha hb he
  have ha' : a < D.length := by omega
  have hb' : b < D.length := by omega
  let v : Fin q → Bool := fun k => D[a+k.val]'(by omega)
  obtain ⟨c, hc, hu⟩ := hD.2 v
  have hav : ∀ k : Fin q, D[((⟨a,ha'⟩ : Fin D.length).val+k.val)%D.length]? = some (v k) := by
    intro k
    dsimp only
    rw [Nat.mod_eq_of_lt (by omega), List.getElem?_eq_getElem (by omega)]
  have hbv : ∀ k : Fin q, D[((⟨b,hb'⟩ : Fin D.length).val+k.val)%D.length]? = some (v k) := by
    intro k
    dsimp only
    rw [Nat.mod_eq_of_lt (by omega), ← he k.val k.isLt]
    simpa only [Fin.val_mk, Nat.mod_eq_of_lt (by omega : a+k.val < D.length)] using hav k
  exact congrArg Fin.val ((hu ⟨a,ha'⟩ hav).trans (hu ⟨b,hb'⟩ hbv).symm)

/-- A seed satisfying both the manuscript's cyclic statement and the linear
property used by the counting proof. -/
theorem lower_bound_cyclic_seed_exists (r : Nat) (hr : 1 ≤ r) :
    ∃ D : List Bool, D.length = (2^r)^2 ∧ UniqueWindows D (2*r) ∧ CyclicDeBruijn D (2*r) := by
  obtain ⟨D, hD⟩ := cyclic_deBruijn_exists (2*r) (by omega)
  refine ⟨D, ?_, hD.uniqueWindows D (2*r) (by omega), hD⟩
  rw [hD.1, ← Nat.pow_mul]
  congr 1
  omega

end GreedyLowerBound
