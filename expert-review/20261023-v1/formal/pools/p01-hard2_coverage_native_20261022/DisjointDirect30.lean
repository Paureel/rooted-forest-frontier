import DisjointOverlap27
open RMAF Universal233 CherryBranching OrdinaryDispatch
namespace FreshLiteralDisjoint
/-- CONTACTED: adjacent original direct_exact body was accidentally exposed before this author proof.
Only the separately licensed parent_agreement/rejected_lower_bound roots are used; no fresh reconstruction credit. -/
theorem direct_from_parent_checks (T S : Tree) (P : List (List Nat)) (q : Nat)
 (same : ∀x,x∈leaves T ↔ x∈leaves S)
 (part : partitionCheck (leaves S) P=true)
 (et : pairwiseEmbeddings T P=true) (es : pairwiseEmbeddings S P=true)
 (good : P.all (restrictionAgrees T S)=true) (three : P.length=3)
 (pretest : DepthOne.pretest01 T S=.rejected) : QueryExact T S q (DisjointParents.direct P q) := by
 have valid:=DisjointParents.parent_agreement T S P same part et es good
 have lower:=DepthOne.rejected_lower_bound T S pretest
 unfold DisjointParents.direct
 by_cases pay : P.length-1≤q
 · rw [if_pos pay]
   exact ⟨valid,pay,by intro G hG;have low:=lower G hG;omega⟩
 · rw [if_neg pay]
   intro G hG
   have low:=lower G hG
   omega

theorem actual_disjoint_all_good_route (actual : DisjointParents.Ordinary) (T S : Tree)
 (c d : Candidate) (q : Nat)
 (picked : Hard2Overlap.runHard2 T S c=some .disjoint)
 (good : (pendantPartition S c.a c.b).all (restrictionAgrees T S)=true) :
 Hard2Dispatcher.run actual T S c d q=DisjointParents.direct (pendantPartition S c.a c.b) q := by
 unfold Hard2Dispatcher.run
 rw [picked]
 simp only [Hard2Dispatcher.run.match_1,Hard2Dispatcher.run._sparseCasesOn_1,good]
 rfl
end FreshLiteralDisjoint

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshLiteralDisjoint.direct_from_parent_checks
#print axioms FreshLiteralDisjoint.direct_from_parent_checks
#check @FreshLiteralDisjoint.actual_disjoint_all_good_route
#print axioms FreshLiteralDisjoint.actual_disjoint_all_good_route
