import Std

/-!
Local isProtected-edge correctness algebra for Whidden 2013, pp. 115–116.
`Optimal s` is an arbitrary explicit predicate on cut sets. The graph-theoretic
exchange theorem remains an explicit hypothesis; this file does not assert
that actual forests satisfy it. The two-pendant exchange hypothesis is exactly
what the source tries to derive from Lemmas 6.4 and 6.5.
-/
namespace ThesisCorrectness

variable {Edge : Type} {Cut : Type}

/-- A concrete three-branch covering property, including the pendant-pair branch. -/
def Cover (Optimal : Cut → Prop) (has : Cut → Edge → Prop)
    (a b₁ b₂ c : Edge) : Prop :=
  ∀ s, Optimal s → has s a ∨ (has s b₁ ∧ has s b₂) ∨ has s c

/-- A two-pendant exchange: an optimum cutting an endpoint and either pendant
edge can be replaced by an optimum cutting both pendant edges. -/
def PendantExchange (Optimal : Cut → Prop) (has : Cut → Edge → Prop)
    (endpoint b₁ b₂ : Edge) : Prop :=
  ∀ s, Optimal s → has s endpoint → (has s b₁ ∨ has s b₂) →
    ∃ t, Optimal t ∧ has t b₁ ∧ has t b₂

/-- Ordinary A2BC: if earlier A and BB branches have no optimum, every
remaining optimum uses C and avoids all three newly isProtected edges. -/
theorem a2bc_third_branch
    (Optimal : Cut → Prop) (has : Cut → Edge → Prop) (a b₁ b₂ c : Edge)
    (cover : Cover Optimal has a b₁ b₂ c)
    (exchange : PendantExchange Optimal has c b₁ b₂)
    (noA : ¬ ∃ s, Optimal s ∧ has s a)
    (noBB : ¬ ∃ s, Optimal s ∧ has s b₁ ∧ has s b₂)
    (s : Cut) (hs : Optimal s) :
    has s c ∧ ¬ has s a ∧ ¬ has s b₁ ∧ ¬ has s b₂ := by
  have ha : ¬ has s a := fun h => noA ⟨s, hs, h⟩
  have hbb : ¬ (has s b₁ ∧ has s b₂) := fun h => noBB ⟨s, hs, h.1, h.2⟩
  have hc : has s c := by
    rcases cover s hs with h | h | h
    · exact False.elim (ha h)
    · exact False.elim (hbb h)
    · exact h
  have hb₁ : ¬ has s b₁ := fun h => noBB (exchange s hs hc (Or.inl h))
  have hb₂ : ¬ has s b₂ := fun h => noBB (exchange s hs hc (Or.inr h))
  exact ⟨hc, ha, hb₁, hb₂⟩

/-- A2BC's omitted isProtected-c/cut-a form: assuming inherited protection has
already excluded C, failure of the earlier BB branch makes every optimum
use A while avoiding both newly isProtected pendant edges. -/
theorem a2bc_protected_c_branch
    (Optimal : Cut → Prop) (has : Cut → Edge → Prop) (a b₁ b₂ c : Edge)
    (cover : Cover Optimal has a b₁ b₂ c)
    (exchange : PendantExchange Optimal has a b₁ b₂)
    (noC : ¬ ∃ s, Optimal s ∧ has s c)
    (noBB : ¬ ∃ s, Optimal s ∧ has s b₁ ∧ has s b₂)
    (s : Cut) (hs : Optimal s) :
    has s a ∧ ¬ has s c ∧ ¬ has s b₁ ∧ ¬ has s b₂ := by
  have hc : ¬ has s c := fun h => noC ⟨s, hs, h⟩
  have hbb : ¬ (has s b₁ ∧ has s b₂) := fun h => noBB ⟨s, hs, h.1, h.2⟩
  have ha : has s a := by
    rcases cover s hs with h | h | h
    · exact h
    · exact False.elim (hbb h)
    · exact False.elim (hc h)
  have hb₁ : ¬ has s b₁ := fun h => noBB (exchange s hs ha (Or.inl h))
  have hb₂ : ¬ has s b₂ := fun h => noBB (exchange s hs ha (Or.inr h))
  exact ⟨ha, hc, hb₁, hb₂⟩

/-- A3BC only protects A. Its exclusion is ordinary earlier-branch failure. -/
theorem a3bc_protect_a
    (Optimal : Cut → Prop) (has : Cut → Edge → Prop) (a : Edge)
    (noA : ¬ ∃ s, Optimal s ∧ has s a) :
    ∀ s, Optimal s → ¬ has s a := by
  intro s hs h
  exact noA ⟨s, hs, h⟩

/-- Branch BCY may omit its isProtected-X branch only when inherited protection
has ruled out every optimum containing X. -/
theorem bcy_drop_protected_uncle
    (Optimal : Cut → Prop) (has : Cut → Edge → Prop)
    (x c y : Edge) (allPendant : Cut → Prop)
    (cover : ∀ s, Optimal s → has s x ∨ allPendant s ∨ (has s c ∧ has s y))
    (noX : ¬ ∃ s, Optimal s ∧ has s x) :
    ∀ s, Optimal s → allPendant s ∨ (has s c ∧ has s y) := by
  intro s hs
  rcases cover s hs with h | h | h
  · exact False.elim (noX ⟨s, hs, h⟩)
  · exact Or.inl h
  · exact Or.inr h

/-- OR-inheritance of edge protection under unary suppression. -/
def inherited (isProtected : Edge → Bool) : List Edge → Bool
  | [] => false
  | e :: es => isProtected e || inherited isProtected es

theorem inherited_true_iff (isProtected : Edge → Bool) (path : List Edge) :
    inherited isProtected path = true ↔ ∃ e, e ∈ path ∧ isProtected e = true := by
  induction path with
  | nil => simp [inherited]
  | cons e es ih =>
    simp only [inherited, Bool.or_eq_true, ih, List.mem_cons]
    constructor
    · intro h
      rcases h with h | ⟨f, hf, hp⟩
      · exact ⟨e, Or.inl rfl, h⟩
      · exact ⟨f, Or.inr hf, hp⟩
    · rintro ⟨f, hf, hp⟩
      rcases hf with h | h
      · subst f; exact Or.inl hp
      · exact Or.inr ⟨f,h,hp⟩

/-- Suppressing two paths in either order preserves the protection bit. -/
theorem inherited_append (isProtected : Edge → Bool) (left right : List Edge) :
    inherited isProtected (left ++ right) =
      (inherited isProtected left || inherited isProtected right) := by
  induction left with
  | nil => simp [inherited]
  | cons e es ih => simp [inherited, ih, Bool.or_assoc]

/-- Cardinality step in the two-pendant exchange. At most one missing
pendant edge is added; at least one path edge is removed; a parent edge is
restored only after removing at least two. The root case has restored = 0. -/
theorem normalization_cost_le
    (base added removed restored : Nat)
    (hadd : added ≤ 1) (hremove : 1 ≤ removed)
    (hrestore : restored ≤ 1)
    (hone : removed = 1 → restored = 0)
    (havailable : removed ≤ base + added) :
    base + added - removed + restored ≤ base := by
  by_cases h : removed = 1
  · have hz := hone h
    omega
  · omega

#print axioms a2bc_third_branch
#print axioms a2bc_protected_c_branch
#print axioms a3bc_protect_a
#print axioms bcy_drop_protected_uncle
#print axioms inherited_true_iff
#print axioms inherited_append
#print axioms normalization_cost_le
end ThesisCorrectness
