import OuterOptimizer
namespace OrdinaryDispatch.OuterSource
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.FullSourceWork
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.GoodPairGlobalAssembly OrdinaryDispatch.ExtendedSourceAssembly
open Universal233.Hard2Overlap Universal233.PaidAssembly GenericForest.CheckCorrespondence

/-- Nulling only the open local bodies preserves both already closed named
source meters. This is an exact accounting identity on the selected paid arm. -/
theorem paidClosedBody_binding (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (c : CherryBranching.Candidate) (q : Nat) (out : Result) (nd:out≠.disjoint) :
 paidNamedDebit (paidBodyDebit actual (fun _ _ _=>0) ⟨0,fun _=>0⟩ T S c q out) (paidOuterMeter T S c out).value=
 goodPairSelectedDebit actual T S c out q+
 (if hardPaidCaseUsed T S c out then (hardPaidSource actual (fun _ _ _=>0) T S q c out).work else 0) := by
 unfold paidOuterMeter goodPairSelectedDebit hardPaidCaseUsed
 split
 · rename_i p r cuts
   simp only [cuts,hard2ParentsMeter_value]
   cases out with
   | disjoint=>exact False.elim (nd rfl)
   | clique v=>simp [paidNamedDebit,paidBodyDebit]
   | diagonal o v w=>simp [paidNamedDebit,paidBodyDebit]
   | four o v w=>simp [paidNamedDebit,paidBodyDebit]
   | pair o choice=>cases choice with
    | vertex v=>simp [paidNamedDebit,paidBodyDebit]
    | edge edge=>
     simp only [meterRestrictionAgrees_value]
     split
     · simp_all [paidNamedDebit,paidBodyDebit]
     · split <;> simp_all [paidNamedDebit,paidBodyDebit,queryWork_zero]
 · simp_all [paidNamedDebit,paidBodyDebit]

/-- Exact comparison with the pre-existing selected-body summands: adding the
new outerLocalDebit does not add GoodPair or hardPaid a second time. -/
theorem paidClosedBody_local_binding (q : Nat) {T S : Tree} (hp:DepthOne.proper T S=true)
 (pre:DepthOne.pretest01 T S=.rejected) {c d : CherryBranching.Candidate} (he:early T S=.hard2 c d)
 (out : Result) (selected:runHard2 T S c=some out) (nd:out≠.disjoint) :
 paidNamedDebit (paidBodyDebit (cutoff FastOrdinary.solve q) (fun _ _ _=>0) ⟨0,fun _=>0⟩ T S c q out)
  (paidOuterMeter T S c out).value=goodPairLocalDebit T S q+hardPaidLocalDebit T S q := by
 rw [paidClosedBody_binding _ _ _ _ _ _ nd]
 simp only [goodPairLocalDebit,hardPaidLocalDebit,hp,ite_true,pre,he,selected]

/-- Same source split at the actual ordinaryStepTrace call site. Open named
local bodies remain an exact visible residual, never a silently closed bill. -/
theorem actualHard2OuterSource_step_split (W : GenericForest.FrontierWork.OrdinaryWork)
 (openBodies : OpenHandlerResiduals) (q : Nat) {T S : Tree} (hp:DepthOne.proper T S=true)
 (pre:DepthOne.pretest01 T S=.rejected) {c d : CherryBranching.Candidate} (he:early T S=.hard2 c d) :
 (hard2OuterSource (cutoff FastOrdinary.solve q) W (actualNamedFees W openBodies T S c q) T S c q).work=
 (hard2FrontMeter T S c q).work+outerLocalDebit T S q+
 namedRouteDebit (actualNamedFees (fun _ _ _=>0) openBodies T S c q) T S c (hard2FrontMeter T S c q).value+
 queryWork W (ordinaryStepTrace FastOrdinary.solve q T S).queries := by
 rw [outerLocalDebit_binding q hp pre he]
 simpa only [ordinaryStepTrace,hp,ite_true,pre,he] using actualHard2OuterSource_split W openBodies T S c d q
end OrdinaryDispatch.OuterSource
