import GraphRegion
namespace BridgeReview.Controls
open PureBridge

def twoVertices (v : Address) : Prop := v = [] ∨ v = [false]
def skippedParent (v : Address) : Prop := v = [] ∨ v = [false,false]

theorem root_child_walk : Walk twoVertices [] [false] := by
  exact .step (.refl (Or.inl rfl)) (Or.inl ⟨false,rfl⟩) (Or.inr rfl)

theorem child_root_walk : Walk twoVertices [false] [] := by
  exact .step (.refl (Or.inr rfl)) (Or.inr ⟨false,rfl⟩) (Or.inl rfl)

/-- A connected support may contain a shallower vertex; omitting the minimum
condition would wrongly force the child to be an ancestor of its parent. -/
theorem minimum_condition_needed :
    ¬ (∀ (P : Address → Prop) (r y : Address), Walk P r y → r.IsPrefix y) := by
  intro h
  have bad := h twoVertices [false] [] child_root_walk
  have noPrefix : ¬ ([false] : Address).IsPrefix [] := by decide
  exact noPrefix bad

/-- A minimum-depth point of a disconnected list need not be a common
ancestor. Equal-length but distinct vertices expose the missing hypothesis. -/
theorem connectivity_needed :
    ([false] : Address).length ≤ ([true] : Address).length ∧
    ¬ ([false] : Address).IsPrefix [true] := by decide

/-- Graph walks cannot silently suppress an intermediate degree-two vertex. -/
theorem cannot_skip_parent : ¬ Walk skippedParent [] [false,false] := by
  intro w
  have hm := walk_ancestor_between w [false] (by decide) (by decide)
  change [false] = ([] : Address) ∨ [false] = ([false,false] : Address) at hm
  rcases hm with h | h <;> cases h

/-- The unsuppressed root-to-grandchild path retains its middle vertex. -/
theorem middle_vertex_retained (P : Address → Prop) (w : Walk P [] [false,false]) :
    P [false] := walk_ancestor_between w [false] (by decide) (by decide)

#print axioms root_child_walk
#print axioms child_root_walk
#print axioms minimum_condition_needed
#print axioms connectivity_needed
#print axioms cannot_skip_parent
#print axioms middle_vertex_retained
end BridgeReview.Controls
