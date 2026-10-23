import Std
/- Local repair of the quantifier interface; this does not prove AF coverage,
exchange, state invariants, or optimal-completion transport. -/
namespace CorrectnessReview
variable {Edge Cut : Type}
def Exchange (Optimal : Cut → Prop) (has : Cut → Edge → Prop)
    (endpoint b₁ b₂ : Edge) : Prop :=
  ∀ s, Optimal s → has s endpoint → (has s b₁ ∨ has s b₂) →
    ∃ t, Optimal t ∧ has t b₁ ∧ has t b₂

/-- Every optimum in the C child avoids new pendant protection, provided
no BB optimum exists. This needs only C-child membership, not universal Cover. -/
theorem c_child_exclusion
    (Optimal : Cut → Prop) (has : Cut → Edge → Prop) (a b₁ b₂ c : Edge)
    (exchange : Exchange Optimal has c b₁ b₂)
    (noA : ¬ ∃ s, Optimal s ∧ has s a)
    (noBB : ¬ ∃ s, Optimal s ∧ has s b₁ ∧ has s b₂)
    (s : Cut) (hs : Optimal s) (hc : has s c) :
    ¬ has s a ∧ ¬ has s b₁ ∧ ¬ has s b₂ := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact noA ⟨s, hs, h⟩
  · intro h; exact noBB (exchange s hs hc (Or.inl h))
  · intro h; exact noBB (exchange s hs hc (Or.inr h))

/-- Source-style existence of an optimum in some branch suffices to choose C. -/
theorem a2bc_existential_branch
    (Optimal : Cut → Prop) (has : Cut → Edge → Prop) (a b₁ b₂ c : Edge)
    (coverage : ∃ s, Optimal s ∧ (has s a ∨ (has s b₁ ∧ has s b₂) ∨ has s c))
    (exchange : Exchange Optimal has c b₁ b₂)
    (noA : ¬ ∃ s, Optimal s ∧ has s a)
    (noBB : ¬ ∃ s, Optimal s ∧ has s b₁ ∧ has s b₂) :
    ∃ s, Optimal s ∧ has s c ∧ ¬ has s a ∧ ¬ has s b₁ ∧ ¬ has s b₂ := by
  obtain ⟨s, hs, h⟩ := coverage
  have hc : has s c := by
    rcases h with h | h | h
    · exact False.elim (noA ⟨s, hs, h⟩)
    · exact False.elim (noBB ⟨s, hs, h.1, h.2⟩)
    · exact h
  exact ⟨s, hs, hc, c_child_exclusion Optimal has a b₁ b₂ c exchange noA noBB s hs hc⟩

/-- Protected C exchanges the endpoint roles; no universal Cover is needed. -/
theorem protected_c_existential_branch
    (Optimal : Cut → Prop) (has : Cut → Edge → Prop) (a b₁ b₂ c : Edge)
    (coverage : ∃ s, Optimal s ∧ (has s a ∨ (has s b₁ ∧ has s b₂) ∨ has s c))
    (exchange : Exchange Optimal has a b₁ b₂)
    (noC : ¬ ∃ s, Optimal s ∧ has s c)
    (noBB : ¬ ∃ s, Optimal s ∧ has s b₁ ∧ has s b₂) :
    ∃ s, Optimal s ∧ has s a ∧ ¬ has s c ∧ ¬ has s b₁ ∧ ¬ has s b₂ := by
  have reordered : ∃ s, Optimal s ∧ (has s c ∨ (has s b₁ ∧ has s b₂) ∨ has s a) := by
    obtain ⟨s, hs, h⟩ := coverage
    refine ⟨s, hs, ?_⟩
    rcases h with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  exact a2bc_existential_branch Optimal has c b₁ b₂ a reordered exchange noC noBB
#print axioms c_child_exclusion
#print axioms a2bc_existential_branch
#print axioms protected_c_existential_branch
end CorrectnessReview
