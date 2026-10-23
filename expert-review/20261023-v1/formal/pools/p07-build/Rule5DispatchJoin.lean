import Rule5QueryDomains
import ClassifierFeeBinding
import ClassifierFeePolynomial
import HardPaidUniform
namespace OrdinaryDispatch.ExtendedSourceAssembly
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.Hard2SourceWork
open OrdinaryDispatch.WorkRecursion OrdinaryDispatch.WorkIntegration OrdinaryDispatch.GlobalSourceAssembly
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.EarlyLocalWork

/-- Alias of the sealed dispatch body with its two implemented, distinct fees.
The separately owned final rule5Answer caller and local C5 bound are absent. -/
def concreteRule5Dispatch (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (a b q : Nat) :=
 Rule5ExecutionSource.dispatchSource actual W ClassifierCheckFee.checkFee
  (PaidLiteralDecisionWork.literalFee T S a b) T S a b q

theorem concreteRule5Dispatch_value (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (a b q : Nat) :
 (concreteRule5Dispatch actual W T S a b q).value=Rule5OrdinaryDispatch.dispatch actual T S a b q :=
 Rule5ExecutionSource.dispatch_source_value _ _ _ _ _ _ _ _ _

/-- Exact value join only; extracting the answer is not a charged caller. -/
theorem rule5Answer_dispatch_join (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (a b q : Nat) :
 Hard2Dispatcher.rule5Answer actual T S a b q=
 match (concreteRule5Dispatch actual W T S a b q).value with
 | .answered F=>F
 | _=>none := by rw [concreteRule5Dispatch_value];rfl

theorem concreteRule5Dispatch_split (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) :
 (concreteRule5Dispatch actual W T S c.a c.b q).work=
 (concreteRule5Dispatch actual (fun _ _ _=>0) T S c.a c.b q).work+
 queryWork W (hard2RouteQueries actual T S c q .admittedRule5) := by
 have h:=Rule5ExecutionSource.dispatch_source_split actual W ClassifierCheckFee.checkFee
  (PaidLiteralDecisionWork.literalFee T S c.a c.b) T S c.a c.b q
 simpa only [concreteRule5Dispatch,hard2RouteQueries,Rule5ExecutionSource.dispatch_calls_native] using h

/-- An actual Rule5 dispatch-body local bill, kept as an UNBOUNDED residual
until the separately owned concrete local source closure is sealed. -/
def rule5DispatchLocalDebit (T S : Tree) (q : Nat) : Nat :=
 if DepthOne.proper T S then
  match DepthOne.pretest01 T S with
  | .rejected=>match early T S with
   | .hard2 c _=>match (hard2FrontMeter T S c q).value with
    | .admittedRule5=>(concreteRule5Dispatch (cutoff FastOrdinary.solve q) (fun _ _ _=>0) T S c.a c.b q).work
    | _=>0
   | _=>0
  | _=>0
 else 0

theorem rule5DispatchLocal_binding (q : Nat) {T S : Tree} (hp : DepthOne.proper T S=true)
 (pre : DepthOne.pretest01 T S=.rejected) {c d : CherryBranching.Candidate}
 (he : early T S=.hard2 c d) (route : (hard2FrontMeter T S c q).value=.admittedRule5) :
 rule5DispatchLocalDebit T S q=(concreteRule5Dispatch (cutoff FastOrdinary.solve q)
  (fun _ _ _=>0) T S c.a c.b q).work := by
 simp only [rule5DispatchLocalDebit,hp,ite_true,pre,he,route]

theorem rule5Dispatch_actual_step_split (W : OrdinaryWork) (q : Nat) {T S : Tree}
 (hp : DepthOne.proper T S=true) (pre : DepthOne.pretest01 T S=.rejected)
 {c d : CherryBranching.Candidate} (he : early T S=.hard2 c d)
 (route : (hard2FrontMeter T S c q).value=.admittedRule5) :
 (concreteRule5Dispatch (cutoff FastOrdinary.solve q) W T S c.a c.b q).work=
 rule5DispatchLocalDebit T S q+queryWork W (ordinaryStepTrace FastOrdinary.solve q T S).queries := by
 have queries:=hard2FrontMeter_queries (cutoff FastOrdinary.solve q) T S c d q
 rw [route] at queries
 rw [rule5DispatchLocal_binding q hp pre he route,concreteRule5Dispatch_split]
 simp only [ordinaryStepTrace,hp,ite_true,pre,he]
 rw [queries]
end OrdinaryDispatch.ExtendedSourceAssembly
