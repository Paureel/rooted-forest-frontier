import HardPaidSelection
namespace OrdinaryDispatch.ExtendedSourceAssembly
open RMAF Universal233 WholeSourceWork CoreWork Universal233.Hard2Overlap
open GenericForest.FrontierWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.Hard2SourceWork
open OrdinaryDispatch.WorkRecursion OrdinaryDispatch.WorkIntegration OrdinaryDispatch.GlobalSourceAssembly
open OrdinaryDispatch.FastOrdinary

theorem hardPaidLocalDebit_binding (q : Nat) {T S : Tree} (hp : DepthOne.proper T S=true)
 (pre : DepthOne.pretest01 T S=.rejected) {c d : CherryBranching.Candidate}
 (he : early T S=.hard2 c d) {out : Hard2Overlap.Result} (selected : runHard2 T S c=some out)
 (used : hardPaidCaseUsed T S c out=true) :
 hardPaidLocalDebit T S q=(hardPaidSource (cutoff FastOrdinary.solve q)
  (fun _ _ _=>0) T S q c out).work := by
 simp only [hardPaidLocalDebit,hp,ite_true,pre,he,selected,used]

theorem hardPaid_actual_source_value (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (c : CherryBranching.Candidate) (out : Hard2Overlap.Result) (q : Nat)
 (used : hardPaidCaseUsed T S c out=true) :
 (hardPaidSource actual W T S q c out).value=Hard2Dispatcher.paidCase actual T S c q out := by
 rw [hardPaidSource_value,hardPaidCaseUsed_binding actual T S c out q used]

/-- Exact full ordinary callback list. The outer unit calls remain separate
from the paid body's source bill, without dropping either list occurrence. -/
theorem hardPaid_actual_step_queries (q : Nat) {T S : Tree} (hp : DepthOne.proper T S=true)
 (pre : DepthOne.pretest01 T S=.rejected) {c d : CherryBranching.Candidate}
 (he : early T S=.hard2 c d) {out : Hard2Overlap.Result}
 (route : (hard2FrontMeter T S c q).value=.paid out) (used : hardPaidCaseUsed T S c out=true) :
 (ordinaryStepTrace FastOrdinary.solve q T S).queries=
 forestQueries (cutoff FastOrdinary.solve q) (Hard2Combine.unitCalls S T c.a c.b q)++
 forestQueries (cutoff FastOrdinary.solve q)
  (Hard2PaidLocal.runHardPaid (cutoff FastOrdinary.solve q) T S q c out).calls := by
 have queries:=hard2FrontMeter_queries (cutoff FastOrdinary.solve q) T S c d q
 rw [route] at queries
 simp only [ordinaryStepTrace,hp,ite_true,pre,he]
 rw [←queries]
 simp only [hard2RouteQueries,hardPaidCaseUsed_binding _ T S c out q used,Hard2Combine.combine,
  forestQueries,List.flatMap_append]

/-- Paid W-work plus the outer unit callback debit equals the selected paid
local bill plus the complete step's callback debit. This is not a source meter
for the still uncharged combine/selector/other handler bodies. -/
theorem hardPaid_actual_step_split (W : OrdinaryWork) (q : Nat) {T S : Tree}
 (hp : DepthOne.proper T S=true) (pre : DepthOne.pretest01 T S=.rejected)
 {c d : CherryBranching.Candidate} (he : early T S=.hard2 c d) {out : Hard2Overlap.Result}
 (selected : runHard2 T S c=some out) (route : (hard2FrontMeter T S c q).value=.paid out)
 (used : hardPaidCaseUsed T S c out=true) :
 (hardPaidSource (cutoff FastOrdinary.solve q) W T S q c out).work+
 queryWork W (forestQueries (cutoff FastOrdinary.solve q) (Hard2Combine.unitCalls S T c.a c.b q))=
 hardPaidLocalDebit T S q+queryWork W (ordinaryStepTrace FastOrdinary.solve q T S).queries := by
 rw [hardPaidLocalDebit_binding q hp pre he selected used,hardPaid_actual_step_queries q hp pre he route used]
 have split:=hardPaidSource_split (cutoff FastOrdinary.solve q) W T S q c out
 simp only [queryWork,List.map_append,List.sum_append]
 simp only [queryWork] at split
 omega
end OrdinaryDispatch.ExtendedSourceAssembly
