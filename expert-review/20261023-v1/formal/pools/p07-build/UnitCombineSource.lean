import PaidOuterBound
namespace OrdinaryDispatch.OuterSource
open RMAF ForestState Universal233 WholeSourceWork CoreWork Universal233.BothBad
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.FullSourceWork
open Universal233.Rule5SelectedLocalWork Universal233.Rule5PendantLocalWork

def unitChildrenMeter (S : Tree) (a b : Nat) : Rule5LocalWork.Measured (List CherryBranching.Child) :=
 let x:=singletonChildMeter S a;let y:=singletonChildMeter S b
 ⟨[x.value,y.value],x.work+y.work+3⟩

@[simp] theorem unitChildrenMeter_value (S : Tree) (a b : Nat) :
 (unitChildrenMeter S a b).value=[CherryBranching.singletonChild S a,CherryBranching.singletonChild S b] := by
 simp only [unitChildrenMeter,singleton_child_value]

/-- The second literal unit-child construction belongs to unitCalls. The
filterMap examines both entries even when neither is affordable. -/
def unitCallsMeter (S T : Tree) (a b q : Nat) : Charged (List Call) :=
 let cs:=unitChildrenMeter S a b
 ⟨cs.value.filterMap (fun c=>(CherryBranching.remaining q c).map (fun r=>⟨some T,c.sourceForest,r⟩)),
  cs.work+8*cs.value.length+2⟩

@[simp] theorem unitCallsMeter_value (S T : Tree) (a b q : Nat) :
 (unitCallsMeter S T a b q).value=Hard2Combine.unitCalls S T a b q := by
 simp only [unitCallsMeter,unitChildrenMeter_value,Hard2Combine.unitCalls]

theorem unitCalls_length (S T : Tree) (a b q : Nat) : (Hard2Combine.unitCalls S T a b q).length≤2 :=
 List.length_filterMap_le _ _

/-- Paid execution is evaluated by its own named source sheet. Only its
answer/calls are consumed here; no callee work is swallowed into a constant. -/
def combineSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (a b q : Nat) (paid : Execution) : SourceExecution :=
 let cs:=unitChildrenMeter S a b
 let units:=runChildrenSource actual W T S q cs.value
 let calls:=unitCallsMeter S T a b q
 let best:=chooseMeter units.value paid.answer
 ⟨⟨best.value,calls.value++paid.calls⟩,
  cs.work+units.work+calls.work+best.work+calls.value.length+8⟩

theorem combineSource_value (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (a b q : Nat) (paid : Execution) :
 (combineSource actual W T S a b q paid).value=Hard2Combine.combine actual T S a b q paid := by
 simp only [combineSource,unitChildrenMeter_value,runChildrenSource_value,unitCallsMeter_value,chooseMeter_value,
  Hard2Combine.combine]

theorem unit_queries (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree) (a b q : Nat) :
 (childrenTrace actual T S q [CherryBranching.singletonChild S a,CherryBranching.singletonChild S b]).queries=
 forestQueries actual (Hard2Combine.unitCalls S T a b q) := by
 by_cases h:1≤q <;>
  simp [childrenTrace,Rule5ActualTrace.queries,forestQueries,Hard2Combine.unitCalls,Rule5OrdinaryDispatch.forestJobs,
   Rule5OrdinaryDispatch.jobFor,CherryBranching.remaining,CherryBranching.singletonChild,CherryBranching.makeChild,h]

theorem combineSource_split (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (a b q : Nat) (paid : Execution) :
 (combineSource actual W T S a b q paid).work=
 (combineSource actual (fun _ _ _=>0) T S a b q paid).work+
 queryWork W (forestQueries actual (Hard2Combine.unitCalls S T a b q)) := by
 simp only [combineSource,unitChildrenMeter_value,runChildrenSource_value]
 rw [runChildrenSource_split actual W T S q _]
 rw [unit_queries]
 omega

/-- Exact forest overhead at each actual residual q-1. The duplicate a=b case
is still two summands, and q=0 charges no forest solver invocation. -/
theorem unitForestDebit_exact (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (a b q : Nat) :
 childForestDebit actual W T q [CherryBranching.singletonChild S a,CherryBranching.singletonChild S b]=
 if 1≤q then
  forestWork actual W (some T) (CherryBranching.singletonChild S a).sourceForest (q-1)+
  forestWork actual W (some T) (CherryBranching.singletonChild S b).sourceForest (q-1)
 else 0 := by
 by_cases h:1≤q <;>
  simp [childForestDebit,Rule5OrdinaryDispatch.forestJobs,Rule5OrdinaryDispatch.jobFor,
   CherryBranching.remaining,CherryBranching.singletonChild,CherryBranching.makeChild,h]
end OrdinaryDispatch.OuterSource
