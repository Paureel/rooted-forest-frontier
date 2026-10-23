import BothBadPlanSource
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF Universal233 WholeSourceWork CoreWork ForestGroups
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open Universal233.BothBad Universal233.PaidQueries Universal233.Rule5SelectedLocalWork
open OrdinaryDispatch.WorkIntegration OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion

/-- Source construction for both literal left appends; Option failure avoids
those copies. No arbitrary callback payload fee is supplied. -/
def retainedReconstructionMeter (known : List (List Nat)) (completed : List Nat)
 (answer : Option (List (List Nat))) : Charged (Option (List (List Nat))):=
 match answer with
 | none=>⟨none,4⟩
 | some F=>⟨some (known++F++[completed]),4*known.length+2*F.length+16⟩
@[simp] theorem retainedReconstructionMeter_value (known : List (List Nat)) (completed : List Nat)
 (answer : Option (List (List Nat))) :
 (retainedReconstructionMeter known completed answer).value=answer.map (fun F=>known++F++[completed]):=by
 cases answer <;> rfl

def bothBadDispatchLocalSource (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree) (e : Entry) : SourceExecution:=
 match e.mode with
 | .ordinary=>ordinaryLocalSource actual T S e.output.partition e.budget
 | .full=>let ss:=sourceForestMeter S e.output.partition
          ⟨⟨GenericForest.solve actual (some T) ss.value e.budget,[⟨some T,ss.value,e.budget⟩]⟩,ss.work+16⟩
 | .retained _ residual completed known=>
   let t:=localTargetMeter (some T) residual
   let sf:=sourceForestMeter S e.output.partition
   let bs:=ownedMeter sf.value residual
   let a:=GenericForest.solve actual t.value bs.value e.budget
   let f:=retainedReconstructionMeter known completed a
   ⟨⟨f.value,[⟨t.value,bs.value,e.budget⟩]⟩,t.work+sf.work+bs.work+f.work+20⟩
@[simp] theorem bothBadDispatchLocalSource_value (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (e : Entry) :
 (bothBadDispatchLocalSource actual T S e).value=dispatch (GenericForest.solve actual) T S e:=by
 cases hm:e.mode <;> simp only [bothBadDispatchLocalSource,dispatch,hm,ordinaryLocalSource_value,
  source_forest_value,retainedReconstructionMeter_value,localTargetMeter_value,ownedMeter_value] <;> rfl

def bothBadExecuteLocalSource (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (q : Nat) : List Entry→SourceExecution
 | []=>⟨⟨none,[]⟩,2⟩
 | e::es=>let r:=bothBadDispatchLocalSource actual T S e
   let tail:=bothBadExecuteLocalSource actual T S q es
   let checked:=checkedMeter T S q r.value.answer
   let best:=chooseMeter checked.value tail.value.answer
   ⟨⟨best.value,r.value.calls++tail.value.calls⟩,
    r.work+tail.work+checked.work+best.work+2*r.value.calls.length+20⟩
@[simp] theorem bothBadExecuteLocalSource_value (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (q : Nat) (es : List Entry) :
 (bothBadExecuteLocalSource actual T S q es).value=execute (GenericForest.solve actual) T S q es:=by
 induction es with
 | nil=>rfl
 | cons e es ih=>simp only [bothBadExecuteLocalSource,execute,bothBadDispatchLocalSource_value,
   checkedMeter_value,chooseMeter_value,ih]

def bothBadLocalPairLocalSource (actual : GenericForest.FrontierWork.Ordinary) (S T : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) : SourceExecution:=
 let d:=pairDescendantsMeter T edge.2
 let p:=bothBadPlanMeter S T A B C d.value q
 let e:=bothBadExecuteLocalSource actual T S q p.value
 ⟨e.value,d.work+p.work+e.work+12⟩
@[simp] theorem bothBadLocalPairLocalSource_value (actual : GenericForest.FrontierWork.Ordinary) (S T : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) :
 (bothBadLocalPairLocalSource actual S T A B C edge q).value=BothBadLocal.runPair actual S T A B C edge q:=by
 simp only [bothBadLocalPairLocalSource,pairDescendantsMeter_value,bothBadPlanMeter_value,
  bothBadExecuteLocalSource_value,BothBadLocal.runPair,solvePair]

def bothBadLocalPairSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (S T : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) : SourceExecution:=
 let l:=bothBadLocalPairLocalSource actual S T A B C edge q
 ⟨l.value,l.work+callsForestDebit actual W l.value.calls⟩
@[simp] theorem bothBadLocalPairSource_value (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (S T : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) :
 (bothBadLocalPairSource actual W S T A B C edge q).value=BothBadLocal.runPair actual S T A B C edge q:=
 bothBadLocalPairLocalSource_value actual S T A B C edge q

theorem bothBadLocalPairSource_split (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (S T : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) :
 (bothBadLocalPairSource actual W S T A B C edge q).work=
 (bothBadLocalPairSource actual (fun _ _ _=>0) S T A B C edge q).work+
 queryWork W (forestQueries actual (BothBadLocal.runPair actual S T A B C edge q).calls):=by
 have split:=callsForestDebit_split actual W (bothBadLocalPairLocalSource actual S T A B C edge q).value.calls
 simp only [bothBadLocalPairLocalSource_value] at split
 simp only [bothBadLocalPairSource,bothBadLocalPairLocalSource_value]
 omega
end OrdinaryDispatch.Hard2SourceWork
