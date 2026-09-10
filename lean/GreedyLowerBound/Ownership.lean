import GreedyLowerBound.InitialGrammar

set_option autoImplicit false

namespace GreedyLowerBound

/-- A private marker or private nonterminal has a single storage owner.
Primary symbols are deliberately unowned, since they may occur in many
classes while remaining one literal symbol. -/
def UsesClass {κ : Type} (primary : Nat → Prop) (owner : Nat → Option κ)
    (C : κ) (w : Word Nat) : Prop :=
  ∀ a ∈ w, primary a ∨ owner a = some C

/-- A nontarget class uses just one primary, together with its own private
symbols. The designated primary may depend on the class and current phase. -/
def UsesOnePrimary {κ : Type} (owner : Nat → Option κ) (C : κ)
    (X : Nat) (w : Word Nat) : Prop :=
  ∀ a ∈ w, a = X ∨ owner a = some C

theorem UsesClass.private_owner {κ : Type} {primary : Nat → Prop}
    {owner : Nat → Option κ} {C D : κ} {v w : Word Nat} {a : Nat}
    (hw : UsesClass primary owner C w) (hprim : ∀ b, primary b → owner b = none)
    (ha : a ∈ v) (hin : v.IsInfix w) (hown : owner a = some D) : C = D := by
  have hm := hw a (hin.subset ha)
  rcases hm with hm | hm
  · have he := hprim a hm
    rw [he] at hown
    contradiction
  · exact Option.some.inj (hm.symm.trans hown)

theorem UsesClass.scanCount_zero_other_owner {κ : Type} {primary : Nat → Prop}
    {owner : Nat → Option κ} {C D : κ} {v w : Word Nat} {a : Nat}
    (hw : UsesClass primary owner C w) (hprim : ∀ b, primary b → owner b = none)
    (ha : a ∈ v) (hown : owner a = some D) (hne : C ≠ D) : scanCount v w = 0 := by
  have hv : v ≠ [] := by intro he; simp [he] at ha
  by_contra hc
  have hin := (scanCount_is_maximum v w hv).1.factor_isInfix (by omega)
  exact hne (hw.private_owner hprim ha hin hown)

/-- Two distinct primary symbols cannot both occur in one nontarget class.
This is the structural confinement step in Section 4.4. -/
theorem UsesOnePrimary.excludes_mixed {κ : Type} {owner : Nat → Option κ}
    {C : κ} {X a b : Nat} {v w : Word Nat}
    (hw : UsesOnePrimary owner C X w) (ha : a ∈ v) (hb : b ∈ v)
    (hoa : owner a = none) (hob : owner b = none) (hab : a ≠ b) :
    scanCount v w = 0 := by
  have hv : v ≠ [] := by intro he; simp [he] at ha
  by_contra hc
  have hin := (scanCount_is_maximum v w hv).1.factor_isInfix (by omega)
  have hax : a = X := by
    rcases hw a (hin.subset ha) with he | he
    · exact he
    · rw [hoa] at he; contradiction
  have hbx : b = X := by
    rcases hw b (hin.subset hb) with he | he
    · exact he
    · rw [hob] at he; contradiction
  exact hab (hax.trans hbx.symm)

/-- Explicit private-symbol ownership turns local mixed-primary exclusion
into the global target-only frequency equation used by the gain bound. -/
theorem Fragmentation.mixed_primary_frequency {κ : Type} {G : Grammar}
    (P : Fragmentation G) (owner : Nat → Option κ)
    (targets : List (Word Nat)) (other : List (κ × Nat × Word Nat))
    (hp : P.pieces.Perm (targets ++ other.map (fun c => c.2.2)))
    (hother : ∀ c ∈ other, UsesOnePrimary owner c.1 c.2.1 c.2.2)
    (v : Word Nat) (hv : G.Eligible v) (a b : Nat) (ha : a ∈ v) (hb : b ∈ v)
    (hoa : owner a = none) (hob : owner b = none) (hab : a ≠ b) :
    G.frequency v = cellFrequency targets v := by
  rw [P.frequency_eq v hv, (hp.map (scanCount v)).sum_eq]
  change cellFrequency (targets ++ other.map (fun c => c.2.2)) v = _
  rw [cellFrequency_append]
  have hz : cellFrequency (other.map (fun c => c.2.2)) v = 0 := by
    unfold cellFrequency
    rw [List.map_map]
    apply List.sum_eq_zero
    intro n hn
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
    exact (hother c hc).excludes_mixed ha hb hoa hob hab
  rw [hz, Nat.add_zero]

/-- Ownership of a freshly created symbol is assigned once to its class. -/
def extendOwner {κ : Type} (owner : Nat → Option κ) (fresh : Nat) (C : κ) :
    Nat → Option κ := fun a => if a = fresh then some C else owner a

theorem Scan.preserves_class {κ : Type} {v s t : Word Nat} {fresh c : Nat}
    (h : Scan v fresh s t c) (primary : Nat → Prop) (owner : Nat → Option κ)
    (C : κ) (hs : UsesClass primary owner C s) :
    UsesClass primary (extendOwner owner fresh C) C t := by
  intro a ha
  by_cases he : a = fresh
  · exact Or.inr (by simp [extendOwner, he])
  · have hm := h.output_mem a ha
    rcases hm with hm | hm
    · contradiction
    · rcases hs a hm with hp | ho
      · exact Or.inl hp
      · exact Or.inr (by simp [extendOwner, he, ho])

theorem Scan.new_rule_class {κ : Type} {v s t : Word Nat} {fresh c : Nat}
    (h : Scan v fresh s t c) (hc : 0 < c) (hf : fresh ∉ v)
    (primary : Nat → Prop) (owner : Nat → Option κ) (C : κ)
    (hs : UsesClass primary owner C s) :
    UsesClass primary (extendOwner owner fresh C) C v := by
  intro a ha
  have he : a ≠ fresh := by intro he; subst a; exact hf ha
  rcases hs a (h.factor_mem_of_positive hc a ha) with hp | ho
  · exact Or.inl hp
  · exact Or.inr (by simp [extendOwner, he, ho])

theorem UsesClass.extend_other {κ : Type} {primary : Nat → Prop}
    {owner : Nat → Option κ} {C D : κ} {w : Word Nat} {fresh : Nat}
    (hw : UsesClass primary owner C w) (hf : fresh ∉ w) :
    UsesClass primary (extendOwner owner fresh D) C w := by
  intro a ha
  have he : a ≠ fresh := by intro he; subst a; exact hf ha
  rcases hw a ha with hp | ho
  · exact Or.inl hp
  · exact Or.inr (by simp [extendOwner, he, ho])

/-- Full global target exclusion from Section 4.4. Its storage hypotheses
describe literal grammar cells and private ownership, while its target
hypotheses use the verified arithmetic target representation. -/
theorem ActiveStorage.factor_in_target_loses {κ : Type} {G : Grammar}
    (A : Nat → Nat) (t : Nat) (S : ActiveStorage G (A t))
    (owner : Nat → Option κ) (other : List (κ × Nat × Word Nat))
    (hpieces : S.partition.pieces.Perm (S.targets ++ other.map (fun c => c.2.2)))
    (hother : ∀ c ∈ other, UsesOnePrimary owner c.1 c.2.1 c.2.2)
    (hA : Function.Injective A) (howner : ∀ i ≤ t, owner (A i) = none)
    (H n : Nat) (hH : cellMass S.targets ≤ H) (hM : H+64 < S.current.length)
    (hL : S.laterMass < 2*S.current.length) (hd : ∀ u < t, baseDigit n u ≤ 1)
    (v : Word Nat) (hv : G.Eligible v) (hne : v ≠ List.replicate 64 (A t))
    (hc : 0 < scanCount v (targetState n A t)) :
    G.gain v < G.gain (List.replicate 64 (A t)) := by
  rcases targetState_factor_cases n A t hA hd v hv.1 hc with hu | hm
  · have hlen : v.length ≠ 64 := by intro he; exact hne (by simpa [he] using hu)
    have hv' : G.Eligible (List.replicate v.length (A t)) := by rw [← hu]; exact hv
    have hh := S.unary_loses H v.length hH hM hL hlen hv'
    rw [← hu] at hh
    exact hh
  · obtain ⟨a, ha, b, hb, hab, ⟨i, hi, hai⟩, ⟨j, hj, hbj⟩⟩ := hm
    have hoa : owner a = none := by rw [hai]; exact howner i hi
    have hob : owner b = none := by rw [hbj]; exact howner j hj
    have hf := S.partition.mixed_primary_frequency owner S.targets other hpieces hother
      v hv a b ha hb hoa hob hab
    exact S.target_factor_loses H hH hM v hf

end GreedyLowerBound
