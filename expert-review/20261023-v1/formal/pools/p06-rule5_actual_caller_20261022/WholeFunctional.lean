import G0Native
import LiteralTerminal
import ConditionalQuery
import NativeLocalRules
import OriginalRunComplete
import DisjointRule5Join64
import OptimizerBridge

namespace CompletedFunctional233
open RMAF Universal233 OrdinaryDispatch Universal233.CherryBranching

theorem actual_rule5 : FreshLiteralDisjoint.DisjointRule5Clause := by
  intro q T S c d proper pretest early graph below _notAllGood two
  exact CleanRule5Verify20261022.actual_rule5_from_survival
    RootGenericG0.generic_g0_survival q T S c d proper pretest early graph below two

theorem actual_disjoint : ContactedHard2Survival.OriginalDisjointRunRule :=
  FreshLiteralDisjoint.original_disjoint_rule_of_rule5 actual_rule5

theorem actual_hard2 : IndependentReconstruction.Hard2Rule :=
  ContactedHard2Survival.original_hard2_rule_of_disjoint actual_disjoint

/-- Every original ordinary query returns a minimum agreement forest if one
fits q+1 components, and otherwise correctly refuses. All local premises are
inhabited here; none remains a parameter of this theorem. -/
theorem query_correct (q : Nat) (T S : Tree) (proper : DepthOne.proper T S = true) :
    QueryExact T S q (FastOrdinary.solve q T S) :=
  CleanGlobalVerify20261022.conditional_query
    LocalNative.common_ready LocalNative.common_lift LocalNative.one_rule
    LocalNative.high_rule LocalNative.forward_rule4 LocalNative.reverse_rule4
    actual_hard2 LocalNative.reject_impossible q T S proper

theorem malformed_refuses (q : Nat) (T S : Tree)
    (malformed : DepthOne.proper T S = false) : FastOrdinary.solve q T S = none := by
  rw [FastOrdinary.solve.eq_def]
  simp only [malformed,Bool.false_eq_true,ite_false]

/-- k counts components; the actual wrapper guards k=0 and calls q=k-1.
Recovery yields original distinct valid source edges and a minimum forest. -/
theorem external_correct (T S : Tree) (k : Nat) (proper : DepthOne.proper T S = true) :
    FastOrdinary.ExternalExact T S k (FastOrdinary.external T S k) := by
  exact FastOrdinary.externalWith_exact FastOrdinary.solve T S k proper
    (fun _ => query_correct (k-1) T S proper)

theorem optimization_correct (T S : Tree) (proper : DepthOne.proper T S = true) :
    ∃ q F o,
      (BudgetOptimization.optimize T S).search.selected = some (q,F) ∧
      (BudgetOptimization.optimize T S).search.trials =
        BudgetOptimization.failedTrials 0 q ++ [(q,some F)] ∧
      (BudgetOptimization.optimize T S).output = some o ∧
      (BudgetOptimization.optimize T S).recoveries = [(F,some o)] ∧
      FastOrdinary.solve q T S = some F ∧ FinalCutRecovery.recover S F = some o ∧
      agreement T S F = true ∧ agreement T S o.partition = true ∧
      CutRealization.RealizedOutput S o ∧
      o.sourceCuts.Nodup ∧ (∀ e ∈ o.sourceCuts, CoreGraph.Valid S e ∧ e ≠ []) ∧
      o.sourceCuts.length = q ∧ o.partition.length = q+1 ∧
      (∀ G, agreement T S G = true → o.partition.length ≤ G.length) ∧
      q < (leaves T).length :=
  ActualRule5Caller.optimizer_of_query_exact T S proper (fun q => query_correct q T S proper)

theorem malformed_optimizer_refuses (T S : Tree)
    (malformed : DepthOne.proper T S = false) :
    (BudgetOptimization.optimize T S).search.trials = [] ∧
    (BudgetOptimization.optimize T S).recoveries = [] ∧
    (BudgetOptimization.optimize T S).output = none := by
  simp [BudgetOptimization.optimize,malformed]

#check query_correct
#check optimization_correct
#print axioms actual_rule5
#print axioms actual_hard2
#print axioms query_correct
#print axioms external_correct
#print axioms optimization_correct
end CompletedFunctional233
