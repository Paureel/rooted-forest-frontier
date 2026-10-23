import GroupedExecutionSource
import BothBadLocalExecutionSource
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open Universal233.BothBad Universal233.PaidQueries
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion

def badPairLocalSource (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) : SourceExecution:=
 let good:=meterRestrictionAgrees S T C
 if good.value then
  let r:=bothBadLocalPairLocalSource actual S T A B C edge q
  ⟨r.value,good.work+r.work+8⟩
 else
  let r:=groupPairLocalSource actual T S A B C edge q
  ⟨⟨r.value.answer,groupCalls r.value.queries⟩,good.work+r.work+12*r.value.queries.length+12⟩
@[simp] theorem badPairLocalSource_value (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) :
 (badPairLocalSource actual T S A B C edge q).value=Hard2Dispatcher.badPair actual T S A B C edge q:=by
 simp only [badPairLocalSource,Hard2Dispatcher.badPair,meterRestrictionAgrees_value,
  bothBadLocalPairLocalSource_value,groupPairLocalSource_value,Hard2Dispatcher.groupedExecution,groupCalls]
 split <;> rfl

def badPairSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (T S : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) : SourceExecution:=
 let r:=badPairLocalSource actual T S A B C edge q
 ⟨r.value,r.work+callsForestDebit actual W r.value.calls⟩
@[simp] theorem badPairSource_value (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (T S : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) :
 (badPairSource actual W T S A B C edge q).value=Hard2Dispatcher.badPair actual T S A B C edge q:=
 badPairLocalSource_value actual T S A B C edge q

theorem badPairSource_split (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (T S : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) :
 (badPairSource actual W T S A B C edge q).work=
 (badPairSource actual (fun _ _ _=>0) T S A B C edge q).work+
 queryWork W (forestQueries actual (Hard2Dispatcher.badPair actual T S A B C edge q).calls):=by
 have split:=callsForestDebit_split actual W (badPairLocalSource actual T S A B C edge q).value.calls
 simp only [badPairLocalSource_value] at split
 simp only [badPairSource,badPairLocalSource_value]
 omega

/-- This separates the actual concrete local body from the forest debit. The
uniform polynomial bound for that concrete local body remains a separate goal. -/
theorem badPairSource_weighted_forest_debit (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q N Q : Nat) (budget:q≤Q)
 (proper0:∀a,a∈(Hard2Dispatcher.badPair actual T S A B C edge q).calls→ForestState.proper a.target a.sources=true)
 (size:∀a,a∈(Hard2Dispatcher.badPair actual T S A B C edge q).calls→(ForestState.labels a.target).length≤N)
 (residual:∀a,a∈(Hard2Dispatcher.badPair actual T S A B C edge q).calls→a.budget≤q) :
 ((badPairSource actual (fun _ _ _=>0) T S A B C edge q).work:Rat)≤
 ((badPairLocalSource actual T S A B C edge q).work:Rat)+
 (geometric Rule5ActualTrace.base*forestCoefficient N Q*Rule5ActualTrace.base^q)*
 traceMass Rule5ActualTrace.base q (Hard2Dispatcher.badPair actual T S A B C edge q).calls:=by
 have debit:=callsForestDebit_weighted actual (Hard2Dispatcher.badPair actual T S A B C edge q).calls q N Q budget proper0 size residual
 have localRefl:((badPairLocalSource actual T S A B C edge q).work:Rat)≤
  ((badPairLocalSource actual T S A B C edge q).work:Rat):=Rat.le_refl
 simpa only [badPairSource,badPairLocalSource_value,Rat.natCast_add] using
  SourceCoverage.qadd_le_add localRefl debit
end OrdinaryDispatch.Hard2SourceWork
