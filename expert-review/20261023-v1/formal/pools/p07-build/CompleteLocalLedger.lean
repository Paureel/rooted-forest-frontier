import CompleteOrdinaryStep
namespace OrdinaryDispatch.CompleteSource
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.OuterSource
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.GlobalSourceAssembly
open OrdinaryDispatch.GoodPairGlobalAssembly OrdinaryDispatch.ExtendedSourceAssembly
open Universal233.Hard2Overlap Universal233.Rule5ClosedSource

theorem hard2_closed_named_binding (q : Nat) {T S : Tree} (hp:DepthOne.proper T S=true)
 (pre:DepthOne.pretest01 T S=.rejected) {c d : CherryBranching.Candidate} (he:early T S=.hard2 c d) :
 namedRouteDebit (actualNamedFees (fun _ _ _=>0) ⟨0,fun _=>0⟩ T S c q) T S c (hard2FrontMeter T S c q).value=
 goodPairLocalDebit T S q+hardPaidLocalDebit T S q+closedRule5LocalDebit T S q := by
 have paid (out : Result) (hg:runHard2 T S c=some out) (nd:out≠.disjoint) :
  namedRouteDebit (actualNamedFees (fun _ _ _=>0) ⟨0,fun _=>0⟩ T S c q) T S c (hard2FrontMeter T S c q).value=
  goodPairLocalDebit T S q+hardPaidLocalDebit T S q+closedRule5LocalDebit T S q:=by
  have route:(hard2FrontMeter T S c q).value=.paid out:=by
   cases out <;> simp_all [hard2FrontMeter]
  have closed:closedRule5LocalDebit T S q=0:=by simp [closedRule5LocalDebit,hp,pre,he,route]
  rw [route,closed,Nat.add_zero]
  simpa only [namedRouteDebit,actualNamedFees] using paidClosedBody_local_binding q hp pre he out hg nd
 cases hg:runHard2 T S c with
 | none=>simp [hard2FrontMeter,hg,namedRouteDebit,goodPairLocalDebit,hardPaidLocalDebit,closedRule5LocalDebit,hp,pre,he]
 | some out=>cases out with
  | clique v=>exact paid (.clique v) hg (by intro h;cases h)
  | diagonal o v w=>exact paid (.diagonal o v w) hg (by intro h;cases h)
  | four o v w=>exact paid (.four o v w) hg (by intro h;cases h)
  | pair o choice=>exact paid (.pair o choice) hg (by intro h;cases h)
  | disjoint=>
   have gp:goodPairSelectedDebit (cutoff FastOrdinary.solve q) T S c .disjoint q=0:=by
    unfold goodPairSelectedDebit;split <;> rfl
   have hd:hardPaidCaseUsed T S c .disjoint=false:=by unfold hardPaidCaseUsed;split <;> rfl
   cases route:(hard2FrontMeter T S c q).value with
   | refused=>simp [namedRouteDebit,actualNamedFees,goodPairLocalDebit,hardPaidLocalDebit,closedRule5LocalDebit,hp,pre,he,hg,route,gp,hd]
   | direct a=>simp [namedRouteDebit,actualNamedFees,goodPairLocalDebit,hardPaidLocalDebit,closedRule5LocalDebit,hp,pre,he,hg,route,gp,hd]
   | admittedRule5=>simp [namedRouteDebit,actualNamedFees,goodPairLocalDebit,hardPaidLocalDebit,closedRule5LocalDebit,hp,pre,he,hg,route,gp,hd]
   | disjointPaid=>simp [namedRouteDebit,actualNamedFees,goodPairLocalDebit,hardPaidLocalDebit,closedRule5LocalDebit,hp,pre,he,hg,route,gp,hd,queryWork_zero]
   | paid out=>
    have f:=paid_route_facts T S c q out route
    rw [hg] at f
    have eq:out=.disjoint:=Option.some.inj f.1.symm
    exact False.elim (f.2 eq)

theorem hard2CompleteSource_local_decomposition (q : Nat) {T S : Tree} (hp:DepthOne.proper T S=true)
 (pre:DepthOne.pretest01 T S=.rejected) {c d : CherryBranching.Candidate} (he:early T S=.hard2 c d) :
 (hard2CompleteSource (fun _ _ _=>0) T S c q).work=
 (hard2FrontMeter T S c q).work+outerLocalDebit T S q+goodPairLocalDebit T S q+
 hardPaidLocalDebit T S q+closedRule5LocalDebit T S q+
 routeResidualDebit (cutoff FastOrdinary.solve q) T S c q (hard2FrontMeter T S c q).value := by
 rw [hard2CompleteSource_bill,actualHard2OuterSource_split (fun _ _ _=>0) _ T S c d q,
  queryWork_zero,concrete_named_residual_split,hard2_closed_named_binding q hp pre he]
 rw [outerLocalDebit_binding q hp pre he]
 omega

def missingLocalDebit (T S : Tree) (q : Nat) : Nat:=
 if DepthOne.proper T S then
  match DepthOne.pretest01 T S with
  | .rejected=>match early T S with
   | .hard2 c _=>routeResidualDebit (cutoff FastOrdinary.solve q) T S c q (hard2FrontMeter T S c q).value
   | _=>0
  | _=>0
 else 0

/-- Equality to the actual selected full step, not a promotion of partial sheets. -/
theorem completeLocalDebit_decomposition (q : Nat) (T S : Tree) (hp:DepthOne.proper T S=true) :
 completeLocalDebit T S q=outerJoinedLocalDebit T S q+missingLocalDebit T S q := by
 cases pre:DepthOne.pretest01 T S with
 | refused=>simp [completeLocalDebit,ordinaryCompleteStepSource,meterFront_value,front,hp,pre,
   outerJoinedLocalDebit,joinedLocalSourceDebit,extendedLocalDebit,closedLocalDebit,commonLocalDebit,
   simpleLocalDebit,rule4LocalDebit,hard2FrontLocalDebit,hardPaidLocalDebit,goodPairLocalDebit,closedRule5LocalDebit,
   outerLocalDebit,missingLocalDebit]
 | found e=>simp [completeLocalDebit,ordinaryCompleteStepSource,meterFront_value,front,hp,pre,
   outerJoinedLocalDebit,joinedLocalSourceDebit,extendedLocalDebit,closedLocalDebit,commonLocalDebit,
   simpleLocalDebit,rule4LocalDebit,hard2FrontLocalDebit,hardPaidLocalDebit,goodPairLocalDebit,closedRule5LocalDebit,
   outerLocalDebit,missingLocalDebit]
 | rejected=>
   cases he:early T S with
   | common reverse c=>simp [completeLocalDebit,ordinaryCompleteStepSource,meterFront_value,front,hp,pre,he,completeBranchSource,
     outerJoinedLocalDebit,joinedLocalSourceDebit,extendedLocalDebit,closedLocalDebit,commonLocalDebit,
     simpleLocalDebit,rule4LocalDebit,hard2FrontLocalDebit,hardPaidLocalDebit,goodPairLocalDebit,closedRule5LocalDebit,
     outerLocalDebit,missingLocalDebit]
   | one reverse c=>simp [completeLocalDebit,ordinaryCompleteStepSource,meterFront_value,front,hp,pre,he,completeBranchSource,
     outerJoinedLocalDebit,joinedLocalSourceDebit,extendedLocalDebit,closedLocalDebit,commonLocalDebit,
     simpleLocalDebit,rule4LocalDebit,hard2FrontLocalDebit,hardPaidLocalDebit,goodPairLocalDebit,closedRule5LocalDebit,
     outerLocalDebit,missingLocalDebit]
   | high reverse c=>simp [completeLocalDebit,ordinaryCompleteStepSource,meterFront_value,front,hp,pre,he,completeBranchSource,
     outerJoinedLocalDebit,joinedLocalSourceDebit,extendedLocalDebit,closedLocalDebit,commonLocalDebit,
     simpleLocalDebit,rule4LocalDebit,hard2FrontLocalDebit,hardPaidLocalDebit,goodPairLocalDebit,closedRule5LocalDebit,
     outerLocalDebit,missingLocalDebit]
   | rule4Forward s=>simp [completeLocalDebit,ordinaryCompleteStepSource,meterFront_value,front,hp,pre,he,completeBranchSource,
     outerJoinedLocalDebit,joinedLocalSourceDebit,extendedLocalDebit,closedLocalDebit,commonLocalDebit,
     simpleLocalDebit,rule4LocalDebit,hard2FrontLocalDebit,hardPaidLocalDebit,goodPairLocalDebit,closedRule5LocalDebit,
     outerLocalDebit,missingLocalDebit]
   | rule4Reverse s=>simp [completeLocalDebit,ordinaryCompleteStepSource,meterFront_value,front,hp,pre,he,completeBranchSource,
     outerJoinedLocalDebit,joinedLocalSourceDebit,extendedLocalDebit,closedLocalDebit,commonLocalDebit,
     simpleLocalDebit,rule4LocalDebit,hard2FrontLocalDebit,hardPaidLocalDebit,goodPairLocalDebit,closedRule5LocalDebit,
     outerLocalDebit,missingLocalDebit]
   | refused=>simp [completeLocalDebit,ordinaryCompleteStepSource,meterFront_value,front,hp,pre,he,completeBranchSource,
     outerJoinedLocalDebit,joinedLocalSourceDebit,extendedLocalDebit,closedLocalDebit,commonLocalDebit,
     simpleLocalDebit,rule4LocalDebit,hard2FrontLocalDebit,hardPaidLocalDebit,goodPairLocalDebit,closedRule5LocalDebit,
     outerLocalDebit,missingLocalDebit]
   | hard2 c d=>
     have bind:=hard2CompleteSource_local_decomposition q hp pre he
     simp only [completeLocalDebit,ordinaryCompleteStepSource,meterFront_value,front,hp,ite_true,pre,he,completeBranchSource]
     rw [bind]
     simp [outerJoinedLocalDebit,joinedLocalSourceDebit,extendedLocalDebit,closedLocalDebit,
      commonLocalDebit,simpleLocalDebit,rule4LocalDebit,hard2FrontLocalDebit,hp,pre,he,missingLocalDebit,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
end OrdinaryDispatch.CompleteSource
