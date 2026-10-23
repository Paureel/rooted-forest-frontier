import OrdinarySchedulerPayload
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open Universal233.BothBad Universal233.PaidQueries
open OrdinaryDispatch.WorkIntegration OrdinaryDispatch.FullSourceWork
open OrdinaryDispatch.WorkRecursion
open Universal233.Rule5SelectedLocalWork

def disjointQueryLocalSource (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (parts : List (List Nat)) (q : Nat) : SourceExecution:=
 let paid:=parts.length-1
 if paid≤q then
  let r:=ordinaryLocalSource actual T S parts (q-paid)
  let check:=checkedMeter T S q r.value.answer
  ⟨⟨check.value,r.value.calls⟩,parts.length+r.work+check.work+16⟩
 else ⟨⟨none,[]⟩,parts.length+8⟩
@[simp] theorem disjointQueryLocalSource_value (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (parts : List (List Nat)) (q : Nat) :
 (disjointQueryLocalSource actual T S parts q).value=OrdinaryDispatch.DisjointParents.query actual T S parts q:=by
 simp only [disjointQueryLocalSource,OrdinaryDispatch.DisjointParents.query]
 split
 · simp only [checkedMeter_value,ordinaryLocalSource_value]
 · rfl

def disjointQuerySource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (parts : List (List Nat)) (q : Nat) : SourceExecution:=
 let r:=disjointQueryLocalSource actual T S parts q
 ⟨r.value,r.work+callsForestDebit actual W r.value.calls⟩
@[simp] theorem disjointQuerySource_value (actual : GenericForest.FrontierWork.Ordinary)
 (W : OrdinaryWork) (T S : Tree) (parts : List (List Nat)) (q : Nat) :
 (disjointQuerySource actual W T S parts q).value=OrdinaryDispatch.DisjointParents.query actual T S parts q:=
 disjointQueryLocalSource_value actual T S parts q
theorem disjointQuerySource_split (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (parts : List (List Nat)) (q : Nat) :
 (disjointQuerySource actual W T S parts q).work=
 (disjointQuerySource actual (fun _ _ _=>0) T S parts q).work+
 queryWork W (forestQueries actual (OrdinaryDispatch.DisjointParents.query actual T S parts q).calls):=by
 have split:=callsForestDebit_split actual W (disjointQueryLocalSource actual T S parts q).value.calls
 simp only [disjointQueryLocalSource_value] at split
 simp only [disjointQuerySource,disjointQueryLocalSource_value]
 omega

/-- Both singleton builders, the literal pendant partition, checked scheduler,
child executor and final length comparison are included. -/
def disjointRunSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (a b q : Nat) : Charged (Option (List (List Nat))):=
 let x:=singletonChildMeter S a;let y:=singletonChildMeter S b
 let cs:=runChildrenSource actual W T S q [x.value,y.value]
 let p:=Rule5PendantLocalWork.partitionMeter S a b
 let qr:=disjointQuerySource actual W T S p.value q
 let best:=chooseMeter cs.value qr.value.answer
 ⟨best.value,x.work+y.work+cs.work+p.work+qr.work+best.work+12⟩
@[simp] theorem disjointRunSource_value (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (a b q : Nat) :
 (disjointRunSource actual W T S a b q).value=OrdinaryDispatch.DisjointParents.run actual T S a b q:=by
 simp only [disjointRunSource,chooseMeter_value,disjointQuerySource_value,runChildrenSource_value,
 singleton_child_value,Rule5PendantLocalWork.partition_value,OrdinaryDispatch.DisjointParents.run]
theorem disjointRunSource_split (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (a b q : Nat) :
 (disjointRunSource actual W T S a b q).work=
 (disjointRunSource actual (fun _ _ _=>0) T S a b q).work+
 queryWork W (childrenTrace actual T S q [CherryBranching.singletonChild S a,CherryBranching.singletonChild S b]).queries+
 queryWork W (forestQueries actual (OrdinaryDispatch.DisjointParents.query actual T S (CherryBranching.pendantPartition S a b) q).calls):=by
 have cs:=runChildrenSource_split actual W T S q [CherryBranching.singletonChild S a,CherryBranching.singletonChild S b]
 have qr:=disjointQuerySource_split actual W T S (CherryBranching.pendantPartition S a b) q
 simp only [disjointRunSource,singleton_child_value,Rule5PendantLocalWork.partition_value,
 runChildrenSource_value,disjointQuerySource_value]
 omega
end OrdinaryDispatch.Hard2SourceWork
