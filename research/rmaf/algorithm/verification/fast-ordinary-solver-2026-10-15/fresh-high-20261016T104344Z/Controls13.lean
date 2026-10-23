-- One-shot literal controls; new code, no author control/oracle execution.
import Ordinary
import ProperJobs
open RMAF Universal233
namespace OwnHigh
def refinesB (F Q : List (List Nat)) : Bool :=
  F.all fun P => Q.any fun R => P.all fun x => R.contains x
theorem refinesB_correct (F Q : List (List Nat)) :
    refinesB F Q = true ↔ VertexGeometry.Refines F Q := by
  simp [refinesB, VertexGeometry.Refines, List.all_eq_true, List.any_eq_true]
def T0 := Tree.node (.leaf 0) (.leaf 1)
def T1 := Tree.node T0 (.leaf 2)
def S1 := Tree.node (.node (.leaf 0) (.leaf 2)) (.leaf 1)
def T2 := Tree.node T0 (.node (.leaf 2) (.leaf 3))
def S2 := Tree.node (.node (.leaf 0) (.node (.leaf 2) (.leaf 3))) (.leaf 1)
theorem c01 : DepthOne.proper T0 T0 = true ∧ CoreGraph.CherryAt T0 [] 0 1 ∧
    agreement T0 T0 [[0,1]] = true ∧ CherryBranching.cuts T0 0 1 = [] ∧
    CherryBranching.pendantPartition T0 0 1 = [[0,1]] ∧ refinesB [[0,1]] [[0,1]] = true := by unfold CoreGraph.CherryAt; decide
theorem c02 : DepthOne.proper T1 S1 = true ∧ CoreGraph.CherryAt T1 [false] 0 1 ∧
    agreement T1 S1 [[0],[1,2]] = true ∧ CherryBranching.pendantPartition S1 0 1 = [[2],[0,1]] ∧
    ([0] ∈ [[0],[1,2]]) ∧ ¬ ([1] ∈ [[0],[1,2]]) ∧ refinesB [[0],[1,2]] [[2],[0,1]] = false := by unfold CoreGraph.CherryAt; decide
theorem c03 : agreement T1 S1 [[1],[0,2]] = true ∧ ([1] ∈ [[1],[0,2]]) ∧
    ¬ ([0] ∈ [[1],[0,2]]) ∧ refinesB [[1],[0,2]] [[2],[0,1]] = false := by decide
theorem c04 : agreement T1 S1 [[0,1],[2]] = true ∧ ¬ ([0] ∈ [[0,1],[2]]) ∧
    ¬ ([1] ∈ [[0,1],[2]]) ∧ refinesB [[0,1],[2]] [[2],[0,1]] = true ∧
    refinesB [[0,1],[2]] [[0],[1],[2]] = false := by decide
theorem c05 : DepthOne.proper T2 S2 = true ∧ agreement T2 S2 [[0,1],[2],[3]] = true ∧
    CherryBranching.pendantPartition S2 0 1 = [[2,3],[0,1]] ∧
    refinesB [[0,1],[2],[3]] [[2,3],[0,1]] = true := by decide
theorem c06 : agreement T2 S2 [[0,1],[2,3]] = true ∧
    refinesB [[0,1],[2,3]] [[2,3],[0,1]] = true := by decide
theorem c07 : CherryBranching.pendantPartition T1 0 1 = [[0,1,2]] ∧
    ¬ CoreGraph.CherryAt S1 [false] 0 1 := by unfold CoreGraph.CherryAt; decide
theorem c08 : CoreGraph.CherryAt (.node (.leaf 0) (.leaf 0)) [] 0 0 ∧
    DepthOne.proper (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)) = false := by unfold CoreGraph.CherryAt; decide
theorem c09 : DepthOne.proper T0 (.node (.leaf 0) (.leaf 2)) = false ∧
    agreement T0 (.node (.leaf 0) (.leaf 2)) [[0,1]] = false := by decide
theorem c10 : agreement T1 S1 [[0,1,2]] = false := by decide
#print axioms refinesB_correct
#print axioms c01
#print axioms c02
#print axioms c03
#print axioms c04
#print axioms c05
#print axioms c06
#print axioms c07
#print axioms c08
#print axioms c09
#print axioms c10
end OwnHigh
