import CompleteResidualBounds
namespace OrdinaryDispatch.CompleteSource
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.OuterSource
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.EarlyLocalWork

def completeBranchSource (W : GenericForest.FrontierWork.OrdinaryWork) (q : Nat) (T S : Tree) :
 Early T S→Charged (Option (List (List Nat)))
 | .common reverse c=>commonBranchMeter FastOrdinary.solve W q T S reverse c
 | .one reverse c=>let p:=Oriented reverse T S;oneSource (cutoff FastOrdinary.solve q) W p.1 p.2 q c.a c.b
 | .high reverse c=>let p:=Oriented reverse T S;highSource (cutoff FastOrdinary.solve q) W p.1 p.2 q c.a c.b
 | .rule4Forward s=>rule4Source (cutoff FastOrdinary.solve q) W s q
 | .rule4Reverse s=>rule4Source (cutoff FastOrdinary.solve q) W s q
 | .hard2 c _=>hard2CompleteSource W T S c q
 | .refused=>⟨none,0⟩

/-- Actual metered prefix followed by exactly its selected metered source body. -/
def ordinaryCompleteStepSource (W : GenericForest.FrontierWork.OrdinaryWork) (q : Nat) (T S : Tree) :
 Charged (Option (List (List Nat))) :=
 let f:=meterFront q T S
 match f.value with
 | .stop a=>⟨a,f.work⟩
 | .selected e=>let r:=completeBranchSource W q T S e;⟨r.value,f.work+r.work⟩

theorem ordinaryCompleteStepSource_value (W : GenericForest.FrontierWork.OrdinaryWork) (q : Nat) (T S : Tree) :
 (ordinaryCompleteStepSource W q T S).value=(ordinaryStepTrace FastOrdinary.solve q T S).value := by
 simp only [ordinaryCompleteStepSource,meterFront_value,front,ordinaryStepTrace]
 by_cases hp:DepthOne.proper T S=true
 · simp only [hp,ite_true]
   cases pre:DepthOne.pretest01 T S with
   | refused=>rfl
   | found c=>rfl
   | rejected=>cases e:early T S with
    | common reverse c=>simp only [completeBranchSource,commonBranchMeter_value];split <;> rfl
    | one reverse c=>simp only [completeBranchSource,oneSource_value,childrenTrace_value]
    | high reverse c=>simp only [completeBranchSource,highSource_value,childrenTrace_value]
    | rule4Forward s=>simp only [completeBranchSource,rule4Source_value];rfl
    | rule4Reverse s=>simp only [completeBranchSource,rule4Source_value];rfl
    | hard2 c d=>simp only [completeBranchSource,hard2Trace_value];exact hard2CompleteSource_value W T S c d q
    | refused=>rfl
 · simp [hp]

theorem ordinaryCompleteStepSource_solve (W : GenericForest.FrontierWork.OrdinaryWork) (q : Nat) (T S : Tree) :
 (ordinaryCompleteStepSource W q T S).value=FastOrdinary.solve q T S := by
 rw [ordinaryCompleteStepSource_value,ordinaryStepTrace_value]

/-- Every reached query occurrence is retained, including failures/duplicates. -/
theorem ordinaryCompleteStepSource_split (W : GenericForest.FrontierWork.OrdinaryWork) (q : Nat) (T S : Tree) :
 (ordinaryCompleteStepSource W q T S).work=(ordinaryCompleteStepSource (fun _ _ _=>0) q T S).work+
 queryWork W (ordinaryStepTrace FastOrdinary.solve q T S).queries := by
 simp only [ordinaryCompleteStepSource,meterFront_value,front,ordinaryStepTrace]
 by_cases hp:DepthOne.proper T S=true
 · simp only [hp,ite_true]
   cases pre:DepthOne.pretest01 T S with
   | refused=>simp [pre,queryWork]
   | found c=>simp [pre,queryWork]
   | rejected=>
    have sound:=early_sound T S
    cases he:early T S with
    | common reverse c=>
      rw [he] at sound
      have ready:=common_pair_ready hp sound
      have sp:=commonBranchMeter_work_split FastOrdinary.solve W q T S reverse c ready.2
      simp only [completeBranchSource,ready.2,ite_true,queryWork,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
      omega
    | one reverse c=>simp only [completeBranchSource];rw [oneSource_split];omega
    | high reverse c=>simp only [completeBranchSource];rw [highSource_split];omega
    | rule4Forward s=>simp only [completeBranchSource];rw [rule4Source_split];omega
    | rule4Reverse s=>simp only [completeBranchSource];rw [rule4Source_split];omega
    | hard2 c d=>simp only [completeBranchSource];rw [hard2CompleteSource_split W T S c d q];omega
    | refused=>simp [completeBranchSource,queryWork]
 · simp [hp,queryWork]

def completeLocalDebit (T S : Tree) (q : Nat) : Nat := (ordinaryCompleteStepSource (fun _ _ _=>0) q T S).work

theorem ordinaryCompleteStepSource_exact_bill (W : GenericForest.FrontierWork.OrdinaryWork) (q : Nat) (T S : Tree) :
 (ordinaryCompleteStepSource W q T S).work=completeLocalDebit T S q+
 queryWork W (ordinaryStepTrace FastOrdinary.solve q T S).queries := ordinaryCompleteStepSource_split W q T S
end OrdinaryDispatch.CompleteSource
