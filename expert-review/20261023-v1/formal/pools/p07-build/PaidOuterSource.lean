import Hard2FullOutputSource
import ChildrenSourceBound
import PaidCaseExact
namespace OrdinaryDispatch.OuterSource
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.FullSourceWork
open GenericForest.CheckCorrespondence
open Universal233.Hard2Overlap Universal233.PaidAssembly
open Universal233.Rule5SelectedLocalWork Universal233.Rule5PendantLocalWork

/-- The exact named body selected by paidCase. Its cost is a separate residual. -/
inductive PaidRoute where
 | empty
 | good : List Nat→List Nat→List Nat→PaidRoute
 | hard
 | bad : List Nat→List Nat→List Nat→(RMAF.Vertex×RMAF.Vertex)→PaidRoute
 deriving Repr

def paidOuterMeter (T S : Tree) (c : CherryBranching.Candidate) (out : Result) : Charged PaidRoute :=
 match c.originalCuts with
 | [p,r]=>
  let parents:=hard2ParentsMeter S p r
  let A:=parents.value.1;let B:=parents.value.2.1;let C:=parents.value.2.2
  match out with
  | .pair o (.edge edge)=>
   let X:=first o A B C;let Y:=second o A B C;let Z:=third o A B C
   let x:=meterRestrictionAgrees S T X;let y:=meterRestrictionAgrees S T Y
   if x.value && y.value then
    ⟨.good X Y Z,parents.work+x.work+y.work+20⟩
   else
    let x2:=meterRestrictionAgrees S T X;let y2:=meterRestrictionAgrees S T Y
    ⟨if x2.value || y2.value then .hard else .bad X Y Z edge,
     parents.work+x.work+y.work+x2.work+y2.work+28⟩
  | _=>⟨.hard,parents.work+12⟩
 | _=>⟨.empty,8⟩

def paidRouteExecution (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (c : CherryBranching.Candidate) (q : Nat) (out : Result) : PaidRoute→Universal233.BothBad.Execution
 | .empty=>⟨none,[]⟩
 | .good X Y Z=>GoodPairDP.runPair actual T S X Y Z q
 | .hard=>Hard2PaidLocal.runHardPaid actual T S q c out
 | .bad X Y Z edge=>Hard2Dispatcher.badPair actual T S X Y Z edge q

theorem paidOuterMeter_value (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (c : CherryBranching.Candidate) (q : Nat) (out : Result) :
 paidRouteExecution actual T S c q out (paidOuterMeter T S c out).value=
 Hard2Dispatcher.paidCase actual T S c q out := by
 unfold paidOuterMeter
 split
 · rename_i p r h
   rw [Hard2Dispatcher.paidCase,h]
   simp only [hard2ParentsMeter_value]
   cases out with
   | pair o choice=>cases choice with
    | edge edge=>
     simp only [meterRestrictionAgrees_value]
     split
     · simp_all only [paidRouteExecution,ite_true]
     · split <;> simp_all only [paidRouteExecution,ite_true,ite_false]
    | vertex v=>rfl
   | disjoint=>rfl
   | clique v=>rfl
   | diagonal o v w=>rfl
   | four o v w=>rfl
 · unfold Hard2Dispatcher.paidCase
   split <;> simp_all [paidRouteExecution]

def paidNamedDebit (fee : PaidRoute→Nat) : PaidRoute→Nat
 | .empty=>0
 | route=>fee route

/-- No bound on these callee costs is presumed. Each selected body occurs once. -/
def paidCaseSource (actual : GenericForest.FrontierWork.Ordinary) (fee : PaidRoute→Nat)
 (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Result) : SourceExecution :=
 let p:=paidOuterMeter T S c out
 ⟨paidRouteExecution actual T S c q out p.value,p.work+paidNamedDebit fee p.value⟩

theorem paidCaseSource_value (actual : GenericForest.FrontierWork.Ordinary) (fee : PaidRoute→Nat)
 (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Result) :
 (paidCaseSource actual fee T S c q out).value=Hard2Dispatcher.paidCase actual T S c q out :=
 paidOuterMeter_value actual T S c q out

theorem paidCaseSource_exact_split (actual : GenericForest.FrontierWork.Ordinary) (fee : PaidRoute→Nat)
 (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Result) :
 (paidCaseSource actual fee T S c q out).work=
 (paidOuterMeter T S c out).work+paidNamedDebit fee (paidOuterMeter T S c out).value := rfl
end OrdinaryDispatch.OuterSource
