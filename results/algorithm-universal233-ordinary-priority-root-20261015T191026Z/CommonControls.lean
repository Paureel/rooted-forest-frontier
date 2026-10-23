import CommonConsumer
import FinalControls
namespace Universal233.Rule5CommonSelector.Controls
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Local.Pre Rule5Classification Rule5Classification.Controls Rule5FinalClassification Rule5FinalClassification.Controls
set_option maxRecDepth 10000
set_option maxRecDepth 10000

def commonD : BadSelection := ⟨[false,false,true],[false,true],2⟩
example : DepthOne.vertices (.node (.leaf 0) (.leaf 1))=[[],[false],[true]] := by decide
example : OrdinaryCommonSplit.Source.incident commonT (subtreeLabels commonS commonD.badArc)=[[false]] := by decide
example : OrdinaryCommonSplit.Source.incident rootT (subtreeLabels commonS commonD.badArc)=[[false,false,false,true,false,true]] := by decide
example : partitionCheck [0,1,2,3,4,5] [[3,4],[0,1,2],[5]]=true := by decide
example : partitionCheck [0,1,2,3,4,5] [[3,4],[0,1,2,5]]=true := by decide
example : (runCommon commonT commonS 0 1 commonD 5 (fun _ _ _ => none)).isSome=true := by decide
example : (runCommon rootT commonS 0 1 commonD 5 (fun _ _ _ => none)).isSome=true := by decide
example : (commonJobs commonT commonS 0 1 commonD 5).isEmpty=false := by decide
example : (commonJobs commonT commonS 0 1 commonD 5).all (fun j => decide (j.budget<5 ∧ 5-j.budget=1) && DepthOne.proper j.T j.S)=true := by decide
example : (commonJobs rootT commonS 0 1 commonD 5).all (fun j => decide (j.budget<5 ∧ 5-j.budget=1) && DepthOne.proper j.T j.S)=true := by decide
example : 0∈outsideLabels commonS 0 1 commonD ∧ 1∈outsideLabels commonS 0 1 commonD ∧ 2∈outsideLabels commonS 0 1 commonD := by decide
example (budget : Nat) (cb : Tree→Tree→Nat→Option (List (List Nat)))
 (ih : OrdinaryCommonSplit.Source.SourceIH commonT commonS (subtreeLabels commonS commonD.badArc) (outsideLabels commonS 0 1 commonD) commonD.badArc budget cb) :
 ∃answer,runCommon commonT commonS 0 1 commonD budget cb=some answer ∧ OrdinaryCommonSplit.Caller.BoundedExact commonT commonS budget answer :=
 selected_one_bounded_solver common_actual common_admitted common_final budget cb ih
#check selected_one_nonrefusal
#check selected_one_bounded_solver
#check selected_one_job_progress
end Universal233.Rule5CommonSelector.Controls
