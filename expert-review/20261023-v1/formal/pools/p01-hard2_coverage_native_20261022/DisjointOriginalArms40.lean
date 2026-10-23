import DisjointActualGeometry38
open RMAF Universal233 CherryBranching OrdinaryDispatch
namespace FreshLiteralDisjoint
theorem original_all_good_query_exact (q : Nat) (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true) (pretest : DepthOne.pretest01 T S=.rejected)
 (selected : FastOrdinary.early T S=.hard2 c d)
 (picked : Hard2Overlap.runHard2 T S c=some .disjoint)
 (good : (pendantPartition S c.a c.b).all (restrictionAgrees T S)=true) :
 QueryExact T S q (Hard2Dispatcher.run (IndependentReconstruction.OwnPaid q) T S c d q) := by
 obtain ⟨nt,ns,same,pt,ps,et,es,three,fee⟩:=original_disjoint_geometry T S c d proper selected picked
 have route:=actual_disjoint_all_good_route (IndependentReconstruction.OwnPaid q) T S c d q picked good
 exact Eq.mp (congrArg (QueryExact T S q) route.symm)
   (direct_from_parent_checks T S _ q same ps et es good three pretest)

theorem original_parent_query_and_strict (q : Nat) (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true) (selected : FastOrdinary.early T S=.hard2 c d)
 (picked : Hard2Overlap.runHard2 T S c=some .disjoint)
 (below : IndependentReconstruction.BelowBudget q) :
 RefiningQueryExact T S (pendantPartition S c.a c.b) q
   (DisjointParents.query (IndependentReconstruction.OwnPaid q) T S (pendantPartition S c.a c.b) q).answer ∧
 ∀call∈(DisjointParents.query (IndependentReconstruction.OwnPaid q) T S (pendantPartition S c.a c.b) q).calls,
   call.budget<q := by
 obtain ⟨nt,ns,same,pt,ps,et,es,three,fee⟩:=original_disjoint_geometry T S c d proper selected picked
 exact query_parent_contract q below T S _ nt ns pt ps et es three

theorem actual_disjoint_mixed_route (actual : DisjointParents.Ordinary) (T S : Tree)
 (c d : Candidate) (q : Nat) (picked : Hard2Overlap.runHard2 T S c=some .disjoint)
 (good : (pendantPartition S c.a c.b).all (restrictionAgrees T S)=false)
 (notRule5 : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length≠2) :
 Hard2Dispatcher.run actual T S c d q=DisjointParents.run actual T S c.a c.b q := by
 unfold Hard2Dispatcher.run
 rw [picked]
 simp only [Hard2Dispatcher.run.match_1,Hard2Dispatcher.run._sparseCasesOn_1,good,notRule5]
 rfl
end FreshLiteralDisjoint

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshLiteralDisjoint.original_all_good_query_exact
#print axioms FreshLiteralDisjoint.original_all_good_query_exact
#check @FreshLiteralDisjoint.original_parent_query_and_strict
#print axioms FreshLiteralDisjoint.original_parent_query_and_strict
#check @FreshLiteralDisjoint.actual_disjoint_mixed_route
#print axioms FreshLiteralDisjoint.actual_disjoint_mixed_route
