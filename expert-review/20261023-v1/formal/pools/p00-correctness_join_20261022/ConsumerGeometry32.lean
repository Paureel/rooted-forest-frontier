-- Exact actual high consumer geometry, without a residual-solver premise.
import ActualChildren31
open RMAF Universal233 CherryBranching VertexGeometry OrdinaryDispatch FastOrdinary
namespace HighSelector
theorem high_consumer_geometry (T S : Tree) (reverse : Bool) (c : Candidate)
    (hp : DepthOne.proper T S=true) (he : early T S=.high reverse c)
    (F : List (List Nat))
    (hag : agreement (Oriented reverse T S).1 (Oriented reverse T S).2 F=true) :
    ∃ child∈branches (Oriented reverse T S).2 c.a c.b,
      HighChildren.ActualChildFacts (Oriented reverse T S).2 child ∧ Refines F child.partition := by
  obtain ⟨child,hchild,href⟩:=actual_high_geometry T S reverse c hp he F hag
  exact ⟨child,hchild,high_actual_children T S reverse c hp he child hchild,href⟩
def HighGeometryInterface : Prop := ∀ T S reverse c,
  DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected → early T S=.high reverse c →
  ∀ F, agreement (Oriented reverse T S).1 (Oriented reverse T S).2 F=true →
    ∃ child∈branches (Oriented reverse T S).2 c.a c.b,
      HighChildren.ActualChildFacts (Oriented reverse T S).2 child ∧ Refines F child.partition
theorem high_geometry_interface : HighGeometryInterface := by
  intro T S reverse c hp _ he F hag
  exact high_consumer_geometry T S reverse c hp he F hag
#print axioms high_consumer_geometry
#print axioms high_geometry_interface
#check high_consumer_geometry
end HighSelector
