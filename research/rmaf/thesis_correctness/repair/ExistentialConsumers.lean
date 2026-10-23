import ExistentialRepair
/- Conditional consumers of the review's existential interface.
The imported proof is the unchanged reviewer source; its .olean is rebuilt
locally from the exact source path recorded in WORKLOG.md. No forest theorem
is asserted here. In particular `lift` is an explicit graph obligation.
-/
namespace NormalizationRepair
variable {Cut Edge Residual REdge : Type}

/-- BCY requires existence in a branch, not coverage of every raw optimum. -/
theorem bcy_existential
    (Optimal : Cut → Prop) (has : Cut → Edge → Prop)
    (x c y : Edge) (pendants : Cut → Prop)
    (coverage : ∃ s, Optimal s ∧
      (has s x ∨ pendants s ∨ (has s c ∧ has s y)))
    (noX : ¬ ∃ s, Optimal s ∧ has s x) :
    (∃ s, Optimal s ∧ pendants s) ∨
      (∃ s, Optimal s ∧ has s c ∧ has s y) := by
  obtain ⟨s, hs, hx | hb | hcy⟩ := coverage
  · exact False.elim (noX ⟨s,hs,hx⟩)
  · exact Or.inl ⟨s,hs,hb⟩
  · exact Or.inr ⟨s,hs,hcy⟩

/-- Inherited exclusion is transported only through a supplied graph lift.
This theorem deliberately does not manufacture such a lift from OR flags. -/
theorem inherited_exclusion_of_lift
    (Optimal : Cut → Prop) (ResidualOptimal : Residual → Prop)
    (has : Cut → Edge → Prop) (residualHas : Residual → REdge → Prop)
    (origin : Edge) (compressed : REdge)
    (lift : ∀ r, ResidualOptimal r → residualHas r compressed →
      ∃ s, Optimal s ∧ has s origin)
    (noOrigin : ¬ ∃ s, Optimal s ∧ has s origin) :
    ¬ ∃ r, ResidualOptimal r ∧ residualHas r compressed := by
  rintro ⟨r,hr,hcut⟩
  exact noOrigin (lift r hr hcut)

/-- The chosen C optimum avoids both newly protected and previously excluded
edges. Coverage is existential; the inherited predicate stays an assumption. -/
theorem a2bc_existential_with_inherited
    (Optimal : Cut → Prop) (has : Cut → Edge → Prop)
    (a b₁ b₂ c : Edge) (oldProtected : Edge → Prop)
    (coverage : ∃ s, Optimal s ∧
      (has s a ∨ (has s b₁ ∧ has s b₂) ∨ has s c))
    (exchange : CorrectnessReview.Exchange Optimal has c b₁ b₂)
    (noA : ¬ ∃ s, Optimal s ∧ has s a)
    (noBB : ¬ ∃ s, Optimal s ∧ has s b₁ ∧ has s b₂)
    (inherited : ∀ s, Optimal s → ∀ e, oldProtected e → ¬ has s e) :
    ∃ s, Optimal s ∧ has s c ∧
      (¬ has s a ∧ ¬ has s b₁ ∧ ¬ has s b₂) ∧
      (∀ e, oldProtected e → ¬ has s e) := by
  obtain ⟨s,hs,hc,ha,hb₁,hb₂⟩ :=
    CorrectnessReview.a2bc_existential_branch Optimal has a b₁ b₂ c
      coverage exchange noA noBB
  exact ⟨s,hs,hc,⟨ha,hb₁,hb₂⟩,inherited s hs⟩

#print axioms bcy_existential
#print axioms inherited_exclusion_of_lift
#print axioms a2bc_existential_with_inherited
end NormalizationRepair
