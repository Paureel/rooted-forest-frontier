import ForestPretestSource
import LiteralScheduleReceiptSource
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState ForestGroups Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open Universal233.PaidQueries Universal233.GroupedFullQuery
open OrdinaryDispatch.EarlyLocalWork

def groupProblemMeter (T : Option Tree) (ss : List Tree) (U : List Nat) : Charged Problem:=
 let t:=localTargetMeter T U;let s:=ownedMeter ss U
 ⟨⟨U,t.value,s.value⟩,t.work+s.work+12⟩
@[simp] theorem groupProblemMeter_value (T : Option Tree) (ss : List Tree) (U : List Nat) :
 (groupProblemMeter T ss U).value=groupProblem T ss U:=by
 simp only [groupProblemMeter,groupProblem,localTargetMeter_value,ownedMeter_value]

def groupProblemsMeter (T : Option Tree) (ss : List Tree) (Q : List (List Nat)) : Charged (List Problem):=
 meterMap (groupProblemMeter T ss) Q
@[simp] theorem groupProblemsMeter_value (T : Option Tree) (ss : List Tree) (Q : List (List Nat)) :
 (groupProblemsMeter T ss Q).value=groupProblems T ss Q:=by
 simp [groupProblemsMeter,groupProblems]

def groupPrepareOneMeter (p : Problem) : Charged (Option (Job Problem (List (List Nat)))):=
 let pre:=forestPretestMeter p.target p.sources
 match pre.value with
 | .refused=>⟨none,pre.work+8⟩
 | .rejected=>⟨some (.hard p),pre.work+12⟩
 | .found F=>let c:=additionalCostMeter p.sources F
             ⟨some (.resolved p c.value F),pre.work+c.work+16⟩
@[simp] theorem groupPrepareOneMeter_value (p : Problem) :
 (groupPrepareOneMeter p).value=prepareOne p:=by
 simp only [groupPrepareOneMeter,prepareOne,forestPretestMeter_value,additionalCostMeter_value,cost]
 cases h:ForestPretest01.pretest01 p.target p.sources <;> rfl

def groupPrepareMeter : List Problem→Charged (Option (List (Job Problem (List (List Nat)))))
 | []=>⟨some [],2⟩
 | p::ps=>let a:=groupPrepareOneMeter p;let r:=groupPrepareMeter ps
           ⟨a.value.bind (fun j=>r.value.map (j::·)),a.work+r.work+8⟩
@[simp] theorem groupPrepareMeter_value (ps : List Problem) :
 (groupPrepareMeter ps).value=prepare ps:=by
 induction ps with
 | nil=>rfl
 | cons p ps ih=>
   simp only [groupPrepareMeter,prepare,groupPrepareOneMeter_value,ih]
   cases hp:prepareOne p <;> cases ht:prepare ps <;> rfl

def groupCallbackMeter (actual : GenericForest.FrontierWork.Ordinary) (p : Problem) (b : Nat) :
 Charged (Option (Nat×List (List Nat))):=
 let answer:=GenericForest.solve actual p.target p.sources b
 match answer with
 | none=>⟨none,4⟩
 | some F=>let c:=additionalCostMeter p.sources F
           ⟨some (c.value,F),c.work+12⟩
@[simp] theorem groupCallbackMeter_value (actual : GenericForest.FrontierWork.Ordinary) (p : Problem) (b : Nat) :
 (groupCallbackMeter actual p b).value=callback actual p b:=by
 simp only [groupCallbackMeter,callback,additionalCostMeter_value,cost]
 cases h:GenericForest.solve actual p.target p.sources b <;> rfl

def groupJobsForMeter (T S : Tree) (A B C : List Nat) (o : CoreProgram.Output) :
 Charged (Option (List (Job Problem (List (List Nat))))):=
 let ss:=Universal233.Rule5SelectedLocalWork.sourceForestMeter S o.partition
 let ab:=appendLabelsMeter A B
 let groups:=groupProblemsMeter (some T) ss.value [ab.value,C]
 let jobs:=groupPrepareMeter groups.value
 ⟨jobs.value,ss.work+ab.work+groups.work+jobs.work+16⟩
@[simp] theorem groupJobsForMeter_value (T S : Tree) (A B C : List Nat) (o : CoreProgram.Output) :
 (groupJobsForMeter T S A B C o).value=BothBadGrouped.jobsFor T S A B C o:=by
 simp only [groupJobsForMeter,BothBadGrouped.jobsFor,groupPrepareMeter_value,groupProblemsMeter_value,
  appendLabelsMeter_value,Universal233.Rule5SelectedLocalWork.source_forest_value]
 rfl

def groupRunOutputLocalSource (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (A B C : List Nat) (q : Nat) (o : CoreProgram.Output) : Charged BothBadGrouped.OutputResult:=
 if o.sourceCuts.length≤q then
  let j:=groupJobsForMeter T S A B C o
  match j.value with
  | none=>⟨.refused,2*o.sourceCuts.length+j.work+12⟩
  | some js=>let r:=literalScheduleSource (groupCallbackMeter actual) (q-o.sourceCuts.length) js
             ⟨.scheduled r.value,2*o.sourceCuts.length+j.work+r.localWork+r.callbackWork+20⟩
 else ⟨.unaffordable,o.sourceCuts.length+8⟩
@[simp] theorem groupRunOutputLocalSource_value (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (A B C : List Nat) (q : Nat) (o : CoreProgram.Output) :
 (groupRunOutputLocalSource actual T S A B C q o).value=BothBadGrouped.runOutput actual T S A B C q o:=by
 have cb:(fun p b=>(groupCallbackMeter actual p b).value)=callback actual:=by
  funext p b;exact groupCallbackMeter_value actual p b
 simp only [groupRunOutputLocalSource,BothBadGrouped.runOutput,groupJobsForMeter_value,literalScheduleSource_value,cb]
 split
 · cases j:BothBadGrouped.jobsFor T S A B C o <;> rfl
 · rfl
end OrdinaryDispatch.Hard2SourceWork
