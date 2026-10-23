import PrefixSourceWork
import CommonBranchWork
import CommonAgreementConsumer
import OrdinaryCallControls
namespace OrdinaryDispatch.FullSourceWork.Controls
open RMAF ForestState Universal233 WholeSourceWork
open OrdinaryDispatch.EarlyLocalWork

def cherry : Tree:=.node (.leaf 0) (.leaf 1)
def candidate : CherryBranching.Candidate:=⟨[],0,1,[]⟩
def refusal : Nat→Tree→Tree→Option (List (List Nat)):=fun _ _ _=>none

theorem actual_agreement_cases :
 (agreementMeter (.leaf 0) (.leaf 0) [[0]]).value=true ∧
 (agreementMeter (.leaf 0) (.leaf 0) [[0],[0]]).value=false ∧
 (agreementMeter (.leaf 0) (.leaf 1) [[0]]).value=false ∧
 0<(agreementMeter (.leaf 0) (.leaf 0) [[0],[0]]).work := by cbv

theorem common_construction_literal :
 (commonPairMeter cherry cherry false candidate).value=(.leaf 2,.leaf 2) ∧
 (expandCommonMeter cherry cherry false candidate [[2]]).value=[[0,1]] := by cbv

theorem common_failed_charge :
 (commonBranchMeter refusal (fun _ _ _=>1) 0 cherry cherry false candidate).value=none ∧
 (commonBranchMeter refusal (fun _ _ _=>1) 0 cherry cherry false candidate).work=
 (commonBranchMeter refusal (fun _ _ _=>0) 0 cherry cherry false candidate).work+1 := by cbv

theorem weighted_common_literal :
 budgetTreeWork 0 WorkRecursion.Controls.commonT WorkRecursion.Controls.commonS=2 ∧
 budgetTreeWork 1 WorkRecursion.Controls.commonT WorkRecursion.Controls.commonS=233/50 := by
 let p : Tree×Tree := (.node Hard2Dispatcher.Controls.T (.leaf 7),.node Hard2Dispatcher.Controls.S (.leaf 7))
 have root0 : (WorkRecursion.ordinaryStepTrace FastOrdinary.solve 0 WorkRecursion.Controls.commonT WorkRecursion.Controls.commonS).queries=[(p,0)] := by cbv
 have root1 : (WorkRecursion.ordinaryStepTrace FastOrdinary.solve 1 WorkRecursion.Controls.commonT WorkRecursion.Controls.commonS).queries=[(p,1)] := by cbv
 have tail0 : (WorkRecursion.ordinaryStepTrace FastOrdinary.solve 0 p.1 p.2).queries=[] := by cbv
 have tail1 : (WorkRecursion.ordinaryStepTrace FastOrdinary.solve 1 p.1 p.2).queries=[] := by cbv
 constructor
 · rw [budgetTreeWork_eq,root0]
   simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Rat.add_zero]
   rw [budgetTreeWork_eq,tail0]
   decide +kernel
 · rw [budgetTreeWork_eq,root1]
   simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Rat.add_zero]
   rw [budgetTreeWork_eq,tail1]
   decide +kernel

theorem prefix_singleton_literal :
 prefixTreeWork 9 (.leaf 0) (.leaf 0)=(meterFront 9 (.leaf 0) (.leaf 0)).work := by cbv
end OrdinaryDispatch.FullSourceWork.Controls
