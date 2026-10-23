import TerminalConditional

open RMAF Universal233 OrdinaryDispatch

namespace CleanRule5Verify20261022

-- The final interface spells out the component premise literally.
theorem actual_rule5_from_survival
    (survival : ∀ (T S : RMAF.Tree)
      (D : Universal233.Case322PaidGuard.LiteralGeometry T S)
      (G : List (List Nat)), RMAF.agreement T S G = true →
      ∃ c ∈ Universal233.Case322PaidGuard.guardedPlan D,
      ∃ H, RMAF.agreement T S H = true ∧ H.length ≤ G.length ∧
        VertexGeometry.Refines H c.partition) :
    ∀ (q : Nat) (T S : Tree) (c d : CherryBranching.Candidate),
      DepthOne.proper T S = true → DepthOne.pretest01 T S = .rejected →
      FastOrdinary.early T S = .hard2 c d →
      Hard2Overlap.runHard2 T S c = some .disjoint →
      IndependentReconstruction.BelowBudget q →
      ((CherryBranching.pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length = 2 →
      QueryExact T S q (Hard2Dispatcher.rule5Answer (IndependentReconstruction.OwnPaid q)
        T S c.a c.b q) := by
  exact terminal_rule5 survival

set_option pp.fullNames true in
#check actual_rule5_from_survival
#print axioms actual_rule5_from_survival

end CleanRule5Verify20261022
