import GoodPairLocalJoin
namespace OrdinaryDispatch.GoodPairGlobalAssembly
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.Hard2SourceWork
open OrdinaryDispatch.WorkRecursion OrdinaryDispatch.WorkIntegration OrdinaryDispatch.GlobalSourceAssembly
open OrdinaryDispatch.ExtendedSourceAssembly OrdinaryDispatch.FastOrdinary
open Universal233.Hard2Overlap Universal233.PaidAssembly

theorem goodPair_paidCase_binding (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (c : CherryBranching.Candidate) (o : Order) (edge : RMAF.Vertex×RMAF.Vertex)
 (p r : RMAF.Vertex) (q : Nat) (cuts : c.originalCuts=[p,r])
 (good : (restrictionAgrees S T (first o (leftParent S p) (rightParent S r) (rootParent S p r)) &&
 restrictionAgrees S T (second o (leftParent S p) (rightParent S r) (rootParent S p r)))=true) :
 (goodPairSource actual W T S
  (first o (leftParent S p) (rightParent S r) (rootParent S p r))
  (second o (leftParent S p) (rightParent S r) (rootParent S p r))
  (third o (leftParent S p) (rightParent S r) (rootParent S p r)) q).value=
 Hard2Dispatcher.paidCase actual T S c q (.pair o (.edge edge)) := by
 rw [goodPairSource_value]
 simp only [Hard2Dispatcher.paidCase,cuts,good,ite_true]

theorem goodPairLocalDebit_binding (q : Nat) {T S : Tree} (hp : DepthOne.proper T S=true)
 (pre : DepthOne.pretest01 T S=.rejected) {c d : CherryBranching.Candidate} (he : early T S=.hard2 c d)
 (o : Order) (edge : RMAF.Vertex×RMAF.Vertex) (p r : RMAF.Vertex) (cuts : c.originalCuts=[p,r])
 (selected : runHard2 T S c=some (.pair o (.edge edge)))
 (good : (restrictionAgrees S T (first o (leftParent S p) (rightParent S r) (rootParent S p r)) &&
 restrictionAgrees S T (second o (leftParent S p) (rightParent S r) (rootParent S p r)))=true) :
 goodPairLocalDebit T S q=(goodPairSource (cutoff FastOrdinary.solve q) (fun _ _ _=>0) T S
  (first o (leftParent S p) (rightParent S r) (rootParent S p r))
  (second o (leftParent S p) (rightParent S r) (rootParent S p r))
  (third o (leftParent S p) (rightParent S r) (rootParent S p r)) q).work ∧ hardPaidLocalDebit T S q=0 := by
 simp only [goodPairLocalDebit,hardPaidLocalDebit,hp,ite_true,pre,he,selected,goodPairSelectedDebit,
  hardPaidCaseUsed,cuts,good,Bool.false_eq_true,ite_false]
 constructor <;> trivial

theorem goodPair_actual_step_queries (q : Nat) {T S : Tree} (hp : DepthOne.proper T S=true)
 (pre : DepthOne.pretest01 T S=.rejected) {c d : CherryBranching.Candidate} (he : early T S=.hard2 c d)
 (o : Order) (edge : RMAF.Vertex×RMAF.Vertex) (p r : RMAF.Vertex) (cuts : c.originalCuts=[p,r])
 (route : (hard2FrontMeter T S c q).value=.paid (.pair o (.edge edge)))
 (good : (restrictionAgrees S T (first o (leftParent S p) (rightParent S r) (rootParent S p r)) &&
 restrictionAgrees S T (second o (leftParent S p) (rightParent S r) (rootParent S p r)))=true) :
 (ordinaryStepTrace FastOrdinary.solve q T S).queries=
 forestQueries (cutoff FastOrdinary.solve q) (Hard2Combine.unitCalls S T c.a c.b q)++
 forestQueries (cutoff FastOrdinary.solve q)
  (GoodPairDP.runPair (cutoff FastOrdinary.solve q) T S
   (first o (leftParent S p) (rightParent S r) (rootParent S p r))
   (second o (leftParent S p) (rightParent S r) (rootParent S p r))
   (third o (leftParent S p) (rightParent S r) (rootParent S p r)) q).calls := by
 have queries:=hard2FrontMeter_queries (cutoff FastOrdinary.solve q) T S c d q
 rw [route] at queries
 simp only [ordinaryStepTrace,hp,ite_true,pre,he]
 rw [←queries]
 simp only [hard2RouteQueries,Hard2Dispatcher.paidCase,cuts,good,ite_true,Hard2Combine.combine,
  forestQueries,List.flatMap_append]

theorem goodPair_actual_step_split (W : OrdinaryWork) (q : Nat) {T S : Tree}
 (hp : DepthOne.proper T S=true) (pre : DepthOne.pretest01 T S=.rejected)
 {c d : CherryBranching.Candidate} (he : early T S=.hard2 c d)
 (o : Order) (edge : RMAF.Vertex×RMAF.Vertex) (p r : RMAF.Vertex) (cuts : c.originalCuts=[p,r])
 (selected : runHard2 T S c=some (.pair o (.edge edge)))
 (route : (hard2FrontMeter T S c q).value=.paid (.pair o (.edge edge)))
 (good : (restrictionAgrees S T (first o (leftParent S p) (rightParent S r) (rootParent S p r)) &&
 restrictionAgrees S T (second o (leftParent S p) (rightParent S r) (rootParent S p r)))=true) :
 (goodPairSource (cutoff FastOrdinary.solve q) W T S
  (first o (leftParent S p) (rightParent S r) (rootParent S p r))
  (second o (leftParent S p) (rightParent S r) (rootParent S p r))
  (third o (leftParent S p) (rightParent S r) (rootParent S p r)) q).work+
 queryWork W (forestQueries (cutoff FastOrdinary.solve q) (Hard2Combine.unitCalls S T c.a c.b q))=
 goodPairLocalDebit T S q+queryWork W (ordinaryStepTrace FastOrdinary.solve q T S).queries := by
 rw [(goodPairLocalDebit_binding q hp pre he o edge p r cuts selected good).1,
  goodPair_actual_step_queries q hp pre he o edge p r cuts route good]
 have split:=goodPairSource_split (cutoff FastOrdinary.solve q) W T S
  (first o (leftParent S p) (rightParent S r) (rootParent S p r))
  (second o (leftParent S p) (rightParent S r) (rootParent S p r))
  (third o (leftParent S p) (rightParent S r) (rootParent S p r)) q
 simp only [queryWork,List.map_append,List.sum_append]
 simp only [queryWork] at split
 omega
end OrdinaryDispatch.GoodPairGlobalAssembly
