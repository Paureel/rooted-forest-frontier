import Hard2FrontTreeSource
import Rule4BoundInterface
namespace OrdinaryDispatch.GlobalSourceAssembly.Controls
open RMAF ForestState Universal233 GenericForest.FrontierWork
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion

def commonT : Tree:=.node Hard2Dispatcher.Controls.T (.node (.leaf 5) (.leaf 6))
def commonS : Tree:=.node Hard2Dispatcher.Controls.S (.node (.leaf 5) (.leaf 6))

theorem weighted_common_literal :
 budgetTreeWork 0 commonT commonS=2 ∧ budgetTreeWork 1 commonT commonS=233/50 := by
 let p : Tree×Tree := (.node Hard2Dispatcher.Controls.T (.leaf 7),.node Hard2Dispatcher.Controls.S (.leaf 7))
 have root0 : (ordinaryStepTrace FastOrdinary.solve 0 commonT commonS).queries=[(p,0)] := by cbv
 have root1 : (ordinaryStepTrace FastOrdinary.solve 1 commonT commonS).queries=[(p,1)] := by cbv
 have tail0 : (ordinaryStepTrace FastOrdinary.solve 0 p.1 p.2).queries=[] := by cbv
 have tail1 : (ordinaryStepTrace FastOrdinary.solve 1 p.1 p.2).queries=[] := by cbv
 constructor
 · rw [budgetTreeWork_eq,root0]
   simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Rat.add_zero]
   rw [budgetTreeWork_eq,tail0]
   decide +kernel
 · rw [budgetTreeWork_eq,root1]
   simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Rat.add_zero]
   rw [budgetTreeWork_eq,tail1]
   decide +kernel

theorem duplicate_failed_debit :
 queryWork (fun _ _ _=>1) (forestQueries Hard2Dispatcher.Controls.refusal WorkIntegration.Controls.failedCalls)=2 := by cbv

theorem zero_local_null :
 sourceSubtotal (fun _ _ _=>0) 9 (.leaf 0) (.leaf 0)=0 := by cbv
end OrdinaryDispatch.GlobalSourceAssembly.Controls
