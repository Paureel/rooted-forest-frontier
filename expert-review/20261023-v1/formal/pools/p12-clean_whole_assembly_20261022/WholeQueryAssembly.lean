import ConditionalQuery
import LiteralTerminal
import G0Native
import OriginalRunComplete
import DisjointRule5Join64
import NativeLocalRules

/- One-shot separately authored assembly from exact supplied component interfaces.
   Imported component proof bodies were not read. -/
open RMAF Universal233 OrdinaryDispatch

namespace CleanWholeAssembly20261022

theorem rule5_clause : FreshLiteralDisjoint.DisjointRule5Clause := by
  intro q T S c d proper pretest early graph below _notAll twoGood
  exact CleanRule5Verify20261022.actual_rule5_from_survival
    RootGenericG0.generic_g0_survival q T S c d proper pretest early graph below twoGood

theorem disjoint_run : ContactedHard2Survival.OriginalDisjointRunRule := by
  exact FreshLiteralDisjoint.original_disjoint_rule_of_rule5 rule5_clause

theorem hard2_rule : IndependentReconstruction.Hard2Rule := by
  exact ContactedHard2Survival.original_hard2_rule_of_disjoint disjoint_run

theorem whole_query : ∀ (q : Nat) (T S : RMAF.Tree),
    DepthOne.proper T S = true →
      QueryExact T S q (FastOrdinary.solve q T S) := by
  exact CleanGlobalVerify20261022.conditional_query
    LocalNative.common_ready LocalNative.common_lift
    LocalNative.one_rule LocalNative.high_rule
    LocalNative.forward_rule4 LocalNative.reverse_rule4
    hard2_rule LocalNative.reject_impossible

set_option pp.fullNames true in
#check whole_query
#print axioms whole_query

end CleanWholeAssembly20261022
