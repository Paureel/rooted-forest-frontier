import OrdinaryChildrenSource
import Rule4Trace
namespace OrdinaryDispatch.FullSourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open Universal233.Rule5SelectedLocalWork Universal233.Rule5PendantLocalWork
open Universal233.HardParent GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork

/-- Literal complement: subtree labels are recomputed for each cut and label,
as in Rule4.literalPartition. Full scanning also pays skipped Boolean tails. -/
def rule4OutsideMeter (S : Tree) (cuts : List RMAF.Vertex) (x : Nat) : Charged Bool :=
 meterAll (fun p=>let s:=subtreeLabelsMeter S p;let c:=meterContains x s.value
  ⟨!c.value,s.work+c.work+2⟩) cuts

theorem rule4OutsideMeter_value (S : Tree) (cuts : List RMAF.Vertex) (x : Nat) :
 (rule4OutsideMeter S cuts x).value=cuts.all (fun p=>!(subtreeLabels S p).contains x) := by
 simp [rule4OutsideMeter,subtree_labels_value]

def rule4PartitionMeter (S : Tree) (cuts : List RMAF.Vertex) : Charged (List (List Nat)) :=
 let b:=blocksMeter S cuts;let l:=meterLeaves S
 let c:=meterFilter (rule4OutsideMeter S cuts) l.value
 ⟨b.value++[c.value],b.work+l.work+c.work+b.value.length+4⟩

theorem rule4PartitionMeter_value (S : Tree) (cuts : List RMAF.Vertex) :
 (rule4PartitionMeter S cuts).value=Rule4.literalPartition S cuts := by
 simp [rule4PartitionMeter,Rule4.literalPartition,blocks_value,rule4OutsideMeter_value]

/-- Actual leaf-address search, including the second subtree on a first miss. -/
def leafAddressMeter (a : Nat) : Tree→Charged (Option RMAF.Vertex)
 | .leaf x=>⟨if x=a then some [] else none,4⟩
 | .node l r=>let p:=leafAddressMeter a l
  match p.value with
  | some v=>⟨some (false::v),p.work+4⟩
  | none=>let q:=leafAddressMeter a r;⟨q.value.map (true::·),p.work+q.work+4⟩

theorem leafAddressMeter_value (a : Nat) (S : Tree) :
 (leafAddressMeter a S).value=Rule4.leafAddress a S := by
 induction S with
 | leaf x=>rfl
 | node l r il ir=>cases h:Rule4.leafAddress a l <;> simp [leafAddressMeter,Rule4.leafAddress,il,ir,h]

/-- Build the literal ordered three branches, reusing the exact pendant cut
meter. Selector work was already charged by meterFront, but aHead and the
swapped pendantOriginal expression are evaluated again in this source body. -/
def rule4BranchesMeter {T S : Tree} (s : Rule4.Choice T S) : Charged (List Rule4.Branch) :=
 let a:=leafAddressMeter s.raw.a S;let p:=cutsMeter T s.raw.a s.raw.c
 ⟨[⟨T,S,[s.raw.cHead,s.raw.xHead],false⟩,
   ⟨T,S,[a.value.getD []],false⟩,
   ⟨S,T,p.value,true⟩],a.work+p.work+18⟩

theorem rule4BranchesMeter_value {T S : Tree} (s : Rule4.Choice T S) :
 (rule4BranchesMeter s).value=Rule4.branches s := by
 simp only [rule4BranchesMeter,Rule4.branches,Rule4.aHead,leafAddressMeter_value,cuts_value]
 rfl

/-- Materialize a branch's whole source forest once at its callback site. -/
def rule4StateMeter (b : Rule4.Branch) : Charged (List Tree) :=
 let p:=rule4PartitionMeter b.source b.cuts
 let f:=sourceForestMeter b.source p.value
 ⟨f.value,p.work+f.work+4⟩

theorem rule4StateMeter_value (b : Rule4.Branch) :
 (rule4StateMeter b).value=b.sourceForest := by
 simp only [rule4StateMeter,source_forest_value,rule4PartitionMeter_value,Rule4.Branch.sourceForest,OutputState.sourceForest,Rule4.Branch.partition]

def rule4AnswersSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (q : Nat) : List Rule4.Branch→Charged (List (List (List Nat)))
 | []=>⟨[],1⟩
 | b::bs=>let r:=rule4AnswersSource actual W q bs
  let state:=rule4StateMeter b
  if b.cost≤q then
   let a:=GenericForest.solve actual (some b.target) state.value (q-b.cost)
   ⟨a.toList++r.value,state.work+2*b.cuts.length+8+
     forestWork actual W (some b.target) state.value (q-b.cost)+r.work⟩
  else ⟨r.value,2*b.cuts.length+4+r.work⟩

theorem rule4AnswersSource_value (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (q : Nat) (bs : List Rule4.Branch) :
 (rule4AnswersSource actual W q bs).value=bs.flatMap (fun b=>Rule4.childOutputs b q (OrdinaryDispatch.rule4Child actual)) := by
 induction bs with
 | nil=>rfl
 | cons b bs ih=>
  simp only [rule4AnswersSource,List.flatMap_cons,Rule4.childOutputs,OrdinaryDispatch.rule4Child,rule4StateMeter_value,ih]
  split <;> simp_all

/-- Exact Nat source companion of runRule4, including original branch builders,
affordable-state materialization, failed solver calls and best List.length.
The selected Rule4 caller does not perform an additional agreement check. -/
def rule4Source (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 {T S : Tree} (s : Rule4.Choice T S) (q : Nat) : Charged (Option (List (List Nat))) :=
 let bs:=rule4BranchesMeter s
 let a:=rule4AnswersSource actual W q bs.value
 let b:=bestLengthMeter (fun _=>⟨true,1⟩) a.value
 ⟨b.value,bs.work+a.work+b.work+2⟩

theorem rule4Source_value (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 {T S : Tree} (s : Rule4.Choice T S) (q : Nat) :
 (rule4Source actual W s q).value=OrdinaryDispatch.runRule4 actual s q := by
 simp only [rule4Source,best_length_value,rule4AnswersSource_value,rule4BranchesMeter_value]
 rfl

theorem queryWork_append (W : OrdinaryWork) (a b : List Query) :
 queryWork W (a++b)=queryWork W a+queryWork W b := by
 simp only [queryWork,List.map_append,List.sum_append]

theorem rule4AnswersSource_split (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (q : Nat) (bs : List Rule4.Branch) :
 (rule4AnswersSource actual W q bs).work=(rule4AnswersSource actual (fun _ _ _=>0) q bs).work+
 queryWork W (forestQueries actual (affordableCalls bs Rule4.Branch.target Rule4.Branch.sourceForest Rule4.Branch.cost q)) := by
 induction bs with
 | nil=>rfl
 | cons b bs ih=>
  simp only [rule4AnswersSource,affordableCalls,List.filterMap_cons]
  simp only [affordableCalls,forestQueries] at ih
  by_cases h:b.cost≤q
  · simp only [h,ite_true,rule4StateMeter_value,List.flatMap_cons,forestQueries,queryWork_append] at ih ⊢
    rw [forestWork_split]
    omega
  · simp only [h,ite_false,forestQueries] at ih ⊢
    omega

theorem rule4Source_split (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 {T S : Tree} (s : Rule4.Choice T S) (q : Nat) :
 (rule4Source actual W s q).work=(rule4Source actual (fun _ _ _=>0) s q).work+
 queryWork W (rule4Trace actual s q).queries := by
 have valueEq:=rule4AnswersSource_value actual W q (Rule4.branches s)
 have zeroEq:=rule4AnswersSource_value actual (fun _ _ _=>0) q (Rule4.branches s)
 have split:=rule4AnswersSource_split actual W q (Rule4.branches s)
 simp only [rule4Source,rule4BranchesMeter_value,valueEq,zeroEq]
 change _=_+queryWork W (forestQueries actual (rule4Calls s q))
 simp only [rule4Calls]
 omega
end OrdinaryDispatch.FullSourceWork
