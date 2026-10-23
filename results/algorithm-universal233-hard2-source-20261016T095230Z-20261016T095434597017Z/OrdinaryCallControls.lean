import OrdinaryCallBound
import WorkControls
namespace OrdinaryDispatch.WorkRecursion.Controls
open RMAF ForestState Universal233
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration

def failedRec : Nat→Tree→Tree→Option CommonForest := fun _ _ _=>none
def commonT : Tree := .node Hard2Dispatcher.Controls.T (.node (.leaf 5) (.leaf 6))
def commonS : Tree := .node Hard2Dispatcher.Controls.S (.node (.leaf 5) (.leaf 6))

theorem singleton_nodes : ordinaryCallNodes 0 (.leaf 0) (.leaf 0)=1 := by cbv
theorem malformed_nodes : ordinaryCallNodes 0 (.leaf 0) (.leaf 1)=1 := by cbv

theorem common_zero_literal : DepthOne.proper commonT commonS=true ∧
 DepthOne.pretest01 commonT commonS=.rejected ∧
 ((ordinaryStepTrace failedRec 0 commonT commonS).queries.map fun pb=>(pb.2,(leaves pb.1.1).length))=[(0,6)] ∧
 ordinaryCallNodes 0 commonT commonS=2 := by cbv

theorem failed_duplicate_occurrences :
 (forestQueries Hard2Dispatcher.Controls.refusal WorkIntegration.Controls.failedCalls).length=2 ∧
 queryWork (fun _ _ _=>1) (forestQueries Hard2Dispatcher.Controls.refusal WorkIntegration.Controls.failedCalls)=2 := by cbv

theorem actual_universal_instance :
 (ordinaryCallNodes 0 commonT commonS:Rat)≤callNodeFactor*((leaves commonT).length+1:Nat)*Rule5ActualTrace.base^0 :=
 ordinaryCallNodes_bound 0 commonT commonS common_zero_literal.1
end OrdinaryDispatch.WorkRecursion.Controls
