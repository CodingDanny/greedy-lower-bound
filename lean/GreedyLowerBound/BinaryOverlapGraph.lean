import GreedyLowerBound.DirectedTrails
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
namespace GreedyLowerBound
namespace BinaryOverlap

abbrev Vertex (m : Nat) := Fin m → Bool
abbrev Edge (m : Nat) := Fin (m+1) → Bool

def source (m : Nat) : Edge m → Vertex m := Fin.init
def target (m : Nat) : Edge m → Vertex m := Fin.tail

/-- Move the last letter to the front. This bijection pairs every incoming
edge at a vertex with an outgoing edge at that same vertex. -/
def rotate (m : Nat) : Edge m ≃ Edge m where
  toFun e := Fin.cons (e (Fin.last m)) (Fin.init e)
  invFun e := Fin.snoc (Fin.tail e) (e 0)
  left_inv e := by simp
  right_inv e := by simp

@[simp] theorem target_rotate (m : Nat) (e : Edge m) :
    target m (rotate m e) = source m e := by
  exact Fin.tail_cons _ _

theorem balanced (m : Nat) : Directed.Balanced (source m) (target m) Finset.univ := by
  intro v
  change (∑ e : Edge m, if source m e = v then 1 else 0) =
    ∑ e : Edge m, if target m e = v then 1 else 0
  simpa only [target_rotate] using
    (rotate m).sum_comp (fun e => if target m e = v then (1 : Nat) else 0)

/-- The concatenation of the starting and destination vertices as a total
bit stream; only its first 2m entries are used. -/
def buffer (m : Nat) (x y : Vertex m) (k : Nat) : Bool :=
  if hk : k < m then x ⟨k,hk⟩
  else if hk' : k < 2*m then y ⟨k-m, by omega⟩ else false

def vertexAt (m : Nat) (x y : Vertex m) (k : Nat) : Vertex m :=
  fun i => buffer m x y (k+i.val)
def edgeAt (m : Nat) (x y : Vertex m) (k : Nat) : Edge m :=
  fun i => buffer m x y (k+i.val)

@[simp] theorem source_edgeAt (m : Nat) (x y : Vertex m) (k : Nat) :
    source m (edgeAt m x y k) = vertexAt m x y k := rfl

@[simp] theorem target_edgeAt (m : Nat) (x y : Vertex m) (k : Nat) :
    target m (edgeAt m x y k) = vertexAt m x y (k+1) := by
  funext i
  change buffer m x y (k+(i.val+1)) = buffer m x y (k+1+i.val)
  congr 1 <;> omega

@[simp] theorem vertexAt_zero (m : Nat) (x y : Vertex m) : vertexAt m x y 0 = x := by
  funext i
  simp [vertexAt, buffer, i.isLt]

@[simp] theorem vertexAt_end (m : Nat) (x y : Vertex m) : vertexAt m x y m = y := by
  funext i
  have h₁ : ¬ m+i.val < m := by omega
  have h₂ : m+i.val < 2*m := by omega
  simp [vertexAt, buffer, h₁, h₂]

theorem path_exists (m : Nat) (x y : Vertex m) (k : Nat) :
    ∃ es, Directed.Walk (source m) (target m) (vertexAt m x y 0) es (vertexAt m x y k) := by
  induction k with
  | zero => exact ⟨[], Directed.Walk.nil _⟩
  | succ k ih =>
    obtain ⟨es, hes⟩ := ih
    refine ⟨es ++ [edgeAt m x y k], hes.append ?_⟩
    have h := Directed.Walk.cons (src := source m) (dst := target m)
      (edgeAt m x y k) (Directed.Walk.nil _)
    simpa only [source_edgeAt, target_edgeAt] using h

theorem connected (m : Nat) : Directed.Connected (source m) (target m) Finset.univ := by
  intro x y
  obtain ⟨es, hes⟩ := path_exists m x y m
  exact ⟨es, by simpa using hes, by simp⟩

/-- Every binary word of length m+1 appears exactly once as an edge. -/
theorem edge_tour_exists (m : Nat) :
    ∃ es, Directed.Walk (source m) (target m) (fun _ => false) es (fun _ => false) ∧
      es.Nodup ∧ es.toFinset = Finset.univ ∧ es.length = 2^(m+1) := by
  classical
  obtain ⟨es, hw, hd, hs⟩ := Directed.eulerian_circuit Finset.univ (balanced m) (connected m)
    (fun _ => false)
  refine ⟨es, hw, hd, hs, ?_⟩
  have hh := congrArg Finset.card hs
  rw [List.toFinset_card_of_nodup hd, Finset.card_univ] at hh
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hh

end BinaryOverlap
end GreedyLowerBound
