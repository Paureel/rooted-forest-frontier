-- Exact actual high shape, with two openly missing obligations and no FastSolve import.
import Orientation30
open RMAF OrdinaryDispatch FastOrdinary Universal233 Universal233.CherryBranching
namespace HighCompletion
def HighStateBridge : Prop := ∀ T S reverse c,
 DepthOne.proper T S=true → early T S=.high reverse c →
 ∀child∈branches (Oriented reverse T S).2 c.a c.b,
   ChildStateBridge (Oriented reverse T S).1 (Oriented reverse T S).2 child
def HighRuleFor (ordinary : OrdinarySolver) : Prop := ∀ q T S reverse c,
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected → early T S=.high reverse c →
 BelowBudget ordinary q → QueryExact T S q (runChildren (OwnPaid ordinary q)
   (Oriented reverse T S).1 (Oriented reverse T S).2 q (branches (Oriented reverse T S).2 c.a c.b))
theorem high_rule_consumer (ordinary : OrdinarySolver)
    (forestComplete : ForestCompletionObligation) (stateBridge : HighStateBridge) : HighRuleFor ordinary := by
  intro q T S reverse c hp _ he below
  apply (query_exact_oriented T S reverse q _).mp
  have hchildren:=HighSelector.high_actual_children T S reverse c hp he
  apply run_children_query_exact ordinary q below forestComplete _ _ _
  · intro child hc
    exact (hchildren child hc).2.2.2.2.2
  · exact stateBridge T S reverse c hp he
  · intro G hag
    exact HighSelector.actual_high_geometry T S reverse c hp he G hag
#print axioms high_rule_consumer
#check high_rule_consumer
end HighCompletion
