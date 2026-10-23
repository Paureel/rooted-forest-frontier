import GroupedJobsSource
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open Universal233.BothBad Universal233.PaidQueries Universal233.GroupedFullQuery
open OrdinaryDispatch.WorkIntegration OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion

def groupOutputAnswerMeter (r : BothBadGrouped.OutputResult) : Charged (Option (List (List Nat))):=
 match r with
 | .scheduled s=>let f:=optionFlattenMeter s.value.answers;⟨f.value,f.work+4⟩
 | _=>⟨none,4⟩
@[simp] theorem groupOutputAnswerMeter_value (r : BothBadGrouped.OutputResult) :
 (groupOutputAnswerMeter r).value=r.answer?:=by
 cases r <;> simp only [groupOutputAnswerMeter,BothBadGrouped.OutputResult.answer?,optionFlattenMeter_value]

structure GroupEvaluationSource where
 value : BothBadGrouped.Evaluation
 work : Nat

def groupEvaluateLocalSource (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (A B C : List Nat) (q : Nat) : List CoreProgram.Output→GroupEvaluationSource
 | []=>⟨⟨[],[]⟩,2⟩
 | o::os=>let r:=groupRunOutputLocalSource actual T S A B C q o
   let a:=groupOutputAnswerMeter r.value
   let tail:=groupEvaluateLocalSource actual T S A B C q os
   ⟨⟨a.value.toList++tail.value.candidates,r.value.trace++tail.value.queries⟩,
    r.work+a.work+tail.work+2*r.value.trace.length+20⟩
@[simp] theorem groupEvaluateLocalSource_value (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (A B C : List Nat) (q : Nat) (os : List CoreProgram.Output) :
 (groupEvaluateLocalSource actual T S A B C q os).value=BothBadGrouped.evaluate actual T S A B C q os:=by
 induction os with
 | nil=>rfl
 | cons o os ih=>simp only [groupEvaluateLocalSource,BothBadGrouped.evaluate,groupOutputAnswerMeter_value,
   groupRunOutputLocalSource_value,ih]

def bothBadOutputsMeter (S : Tree) (A B D : List Nat) (q : Nat) : Charged (List CoreProgram.Output):=
 appendOutputsMeter (generatedOutputsMeter S (cheapColorMeter A B D) q)
  (generatedOutputsMeter S (cheapColorMeter B A D) q)
@[simp] theorem bothBadOutputsMeter_value (S : Tree) (A B D : List Nat) (q : Nat) :
 (bothBadOutputsMeter S A B D q).value=BothBad.outputs S A B D q:=by
 have ca:(fun x=>(cheapColorMeter A B D x).value)=BinaryCheap.cheapColor A B D:=funext (cheapColorMeter_value A B D)
 have cb:(fun x=>(cheapColorMeter B A D x).value)=BinaryCheap.cheapColor B A D:=funext (cheapColorMeter_value B A D)
 simp only [bothBadOutputsMeter,appendOutputsMeter_value,generatedOutputsMeter_value,ca,cb]
 rfl

def groupedAcceptedMeter (T S : Tree) (q : Nat) (F : List (List Nat)) : Charged Bool:=
 let a:=agreementMeter T S F
 ⟨a.value&&decide (F.length-1≤q),a.work+F.length+8⟩
@[simp] theorem groupedAcceptedMeter_value (T S : Tree) (q : Nat) (F : List (List Nat)) :
 (groupedAcceptedMeter T S q F).value=BothBadGrouped.accepted T S q F:=by
 simp only [groupedAcceptedMeter,BothBadGrouped.accepted,agreementMeter_value]

def forestLengthMeter (F : List (List Nat)) : Charged Nat:=⟨F.length,F.length+4⟩
@[simp] theorem forestLengthMeter_value (F : List (List Nat)) : (forestLengthMeter F).value=F.length:=rfl

structure GroupPairSourceExecution where
 value : BothBadGrouped.PairExecution
 work : Nat

def groupPairLocalSource (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) : GroupPairSourceExecution:=
 let d:=pairDescendantsMeter T edge.2
 let o:=bothBadOutputsMeter S A B d.value q
 let e:=groupEvaluateLocalSource actual T S A B C q o.value
 let best:=sourceBestMeter forestLengthMeter (groupedAcceptedMeter T S q) e.value.candidates
 ⟨⟨best.value,e.value.queries⟩,d.work+o.work+e.work+best.work+20⟩
@[simp] theorem groupPairLocalSource_value (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) :
 (groupPairLocalSource actual T S A B C edge q).value=BothBadGrouped.executePair actual T S A B C edge q:=by
 have valid:(fun F=>(groupedAcceptedMeter T S q F).value)=BothBadGrouped.accepted T S q:=funext (groupedAcceptedMeter_value T S q)
 have cost:(fun F=>(forestLengthMeter F).value)=List.length:=funext forestLengthMeter_value
 simp only [groupPairLocalSource,BothBadGrouped.executePair,pairDescendantsMeter_value,
  bothBadOutputsMeter_value,groupEvaluateLocalSource_value,sourceBestMeter_value,valid,cost]

def groupCalls (xs : List (Problem×Nat)) : List Call:=xs.map (fun x=>⟨x.1.target,x.1.sources,x.2⟩)
def groupPairSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (T S : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) : GroupPairSourceExecution:=
 let r:=groupPairLocalSource actual T S A B C edge q
 ⟨r.value,r.work+12*r.value.queries.length+4+callsForestDebit actual W (groupCalls r.value.queries)⟩
@[simp] theorem groupPairSource_value (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (T S : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) :
 (groupPairSource actual W T S A B C edge q).value=BothBadGrouped.executePair actual T S A B C edge q:=
 groupPairLocalSource_value actual T S A B C edge q

theorem groupPairSource_split (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (T S : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) :
 (groupPairSource actual W T S A B C edge q).work=
 (groupPairSource actual (fun _ _ _=>0) T S A B C edge q).work+
 queryWork W (forestQueries actual (groupCalls (BothBadGrouped.executePair actual T S A B C edge q).queries)):=by
 have split:=callsForestDebit_split actual W (groupCalls (groupPairLocalSource actual T S A B C edge q).value.queries)
 simp only [groupPairLocalSource_value] at split
 simp only [groupPairSource,groupPairLocalSource_value]
 omega
end OrdinaryDispatch.Hard2SourceWork
