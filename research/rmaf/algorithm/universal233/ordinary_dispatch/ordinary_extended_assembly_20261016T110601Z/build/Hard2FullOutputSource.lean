import Hard2FrontTreeSource
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open GenericForest.CheckCorrespondence OrdinaryDispatch.FullSourceWork
open Universal233.BothBad Universal233.Rule5SelectedLocalWork

def checkedMeter (T S : Tree) (q : Nat) : Option (List (List Nat))→Charged (Option (List (List Nat)))
 | none=>⟨none,2⟩
 | some F=>let a:=agreementMeter T S F
           ⟨if a.value && decide (F.length-1≤q) then some F else none,a.work+F.length+6⟩
@[simp] theorem checkedMeter_value (T S : Tree) (q : Nat) (F : Option (List (List Nat))) :
 (checkedMeter T S q F).value=checked T S q F := by cases F <;> simp [checkedMeter,checked,accept]

def chooseMeter : Option (List (List Nat))→Option (List (List Nat))→Charged (Option (List (List Nat)))
 | none,b=>⟨b,2⟩
 | a,none=>⟨a,2⟩
 | some F,some G=>⟨if F.length≤G.length then some F else some G,F.length+G.length+4⟩
@[simp] theorem chooseMeter_value (F G : Option (List (List Nat))) :
 (chooseMeter F G).value=choose F G := by cases F <;> cases G <;> rfl

structure SourceExecution where
 value : Execution
 work : Nat

/-- Literal full-mode output caller, including entry affordability, source
materialization, original acceptance and minimum selection. The input output
list's GENERATION remains a distinct source obligation, never an assumed fee. -/
def fullOutputsSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (q : Nat) : List CoreProgram.Output→SourceExecution
 | []=>⟨⟨none,[]⟩,2⟩
 | o::os=>
  let r:=fullOutputsSource actual W T S q os
  if o.sourceCuts.length≤q then
   let ss:=sourceForestMeter S o.partition
   let answer:=GenericForest.solve actual (some T) ss.value (q-o.sourceCuts.length)
   let c:=checkedMeter T S q answer;let b:=chooseMeter c.value r.value.answer
   ⟨⟨b.value,⟨some T,ss.value,q-o.sourceCuts.length⟩::r.value.calls⟩,
    2*o.sourceCuts.length+ss.work+forestWork actual W (some T) ss.value (q-o.sourceCuts.length)+
    c.work+b.work+r.work+14⟩
  else ⟨r.value,2*o.sourceCuts.length+r.work+6⟩

theorem fullOutputsSource_value (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (q : Nat) (os : List CoreProgram.Output) :
 (fullOutputsSource actual W T S q os).value=Hard2PaidLocal.runOutputs actual T S q os := by
 induction os with
 | nil=>rfl
 | cons o os ih=>
  simp only [fullOutputsSource,Hard2PaidLocal.runOutputs,entries,Mode.extra,Nat.add_zero,Nat.sub_zero,List.filterMap_cons]
  by_cases h:o.sourceCuts.length≤q
  · simp only [h,ite_true,execute,dispatch,checkedMeter_value,chooseMeter_value,source_forest_value]
    have tail: (fullOutputsSource actual W T S q os).value=execute (GenericForest.solve actual) T S q (entries q .full os):=ih
    rw [tail]
    rfl
  · simp only [h,ite_false]
    exact ih

theorem fullOutputsSource_split (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (q : Nat) (os : List CoreProgram.Output) :
 (fullOutputsSource actual W T S q os).work=(fullOutputsSource actual (fun _ _ _=>0) T S q os).work+
 queryWork W (forestQueries actual (Hard2PaidLocal.runOutputs actual T S q os).calls) := by
 induction os with
 | nil=>rfl
 | cons o os ih=>
  have val: (fullOutputsSource actual W T S q os).value=(fullOutputsSource actual (fun _ _ _=>0) T S q os).value:=
   (fullOutputsSource_value actual W T S q os).trans (fullOutputsSource_value actual (fun _ _ _=>0) T S q os).symm
  have inner:(Hard2PaidLocal.runOutputs actual T S q os).calls=(fullOutputsSource actual (fun _ _ _=>0) T S q os).value.calls:=
   congrArg Execution.calls (fullOutputsSource_value actual (fun _ _ _=>0) T S q os).symm
  rw [inner] at ih
  rw [←fullOutputsSource_value actual (fun _ _ _=>0) T S q (o::os)]
  simp only [fullOutputsSource]
  by_cases h:o.sourceCuts.length≤q
  · simp only [h,ite_true,val,forestQueries,List.flatMap_cons] at ih ⊢
    rw [forestWork_split]
    simp only [queryWork,List.map_append,List.sum_append] at ih ⊢
    omega
  · simp only [h,ite_false,val]
    omega
/-- Actual runHardPaid EXECUTION body, with its exact generated output list.
This theorem does not charge the still separate actualOutputs generation. -/
def hardPaidOutputExecutionSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (q : Nat) (c : CherryBranching.Candidate) (out : Hard2Overlap.Result) : SourceExecution :=
 fullOutputsSource actual W T S q (Hard2PaidLocal.actualOutputs S T c q out)

theorem hardPaidOutputExecutionSource_value (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (q : Nat) (c : CherryBranching.Candidate) (out : Hard2Overlap.Result) :
 (hardPaidOutputExecutionSource actual W T S q c out).value=Hard2PaidLocal.runHardPaid actual T S q c out :=
 fullOutputsSource_value actual W T S q _

theorem hardPaidOutputExecutionSource_split (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (q : Nat) (c : CherryBranching.Candidate) (out : Hard2Overlap.Result) :
 (hardPaidOutputExecutionSource actual W T S q c out).work=
 (hardPaidOutputExecutionSource actual (fun _ _ _=>0) T S q c out).work+
 queryWork W (forestQueries actual (Hard2PaidLocal.runHardPaid actual T S q c out).calls) :=
 fullOutputsSource_split actual W T S q _
end OrdinaryDispatch.Hard2SourceWork
