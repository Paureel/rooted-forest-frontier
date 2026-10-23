import BadPairLocalComplete
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.WorkIntegration
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion

/-- The real three-block source partition itself supplies the lower size cap. -/
theorem badPair_partition_three (S : Tree) (A B C : List Nat) (N : Nat)
 (sn:treeNodes S≤N) (hp:partitionCheck (leaves S) [A,B,C]=true) : 3≤N := by
 have h:=SourceCoverage.partitionCheck_block_bound (leaves S) [A,B,C] hp
 have l:=leaves_nodes S
 simp only [List.length_cons,List.length_nil] at h
 omega

theorem badPairLocalSource_complete_semantic_bound (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q N Q : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (budget:q≤Q)
 (hs:(leaves S).Nodup) (hp:partitionCheck (leaves S) [A,B,C]=true)
 (selected:PairGeometry.choose T A B=some (.edge edge)) :
 ((badPairLocalSource actual T S A B C edge q).work:Rat)≤
 (badPairLocalPolynomial N Q:Rat)*Rule5ActualTrace.base^q :=
 badPairLocalSource_semantic_bound actual T S A B C edge q N Q
  (badPair_partition_three S A B C N sn hp) tn sn budget hs hp selected

theorem badPair_forest_constant :
 geometric Rule5ActualTrace.base*(4*Rule5ActualTrace.base^(-4:Int))=
 (400000000/417428121:Rat) := by decide +kernel

/-- An explicit fixed coefficient multiplying the unchanged degree-eight forest
polynomial; the local polynomial is the sum of the two proved source branches. -/
def badPairSourcePolynomial (N Q : Nat) : Rat :=
 (badPairLocalPolynomial N Q:Rat)+(400000000/417428121:Rat)*forestCoefficient N Q

/-- Actual zero-callback source bill, including semantic residual forest work.
The hypotheses are the literal original three-parent/selected-edge domain. -/
theorem badPairSource_complete_semantic_bound (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q N Q : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (budget:q≤Q)
 (hs:(leaves S).Nodup) (ht:(leaves T).Nodup) (same:∀x,x∈leaves T↔x∈leaves S)
 (hp:partitionCheck (leaves S) [A,B,C]=true) (es:pairwiseEmbeddings S [A,B,C]=true)
 (badA:restrictionAgrees S T A=false) (badB:restrictionAgrees S T B=false)
 (ac:BinaryExchange.Disj T A C) (bc:BinaryExchange.Disj T B C)
 (selected:PairGeometry.choose T A B=some (.edge edge)) :
 ((badPairSource actual (fun _ _ _=>0) T S A B C edge q).work:Rat)≤
 badPairSourcePolynomial N Q*Rule5ActualTrace.base^q := by
 have localBill:=badPairLocalSource_complete_semantic_bound actual T S A B C edge q N Q tn sn budget hs hp selected
 have forest:=badPairSource_semantic_forest_bound actual T S A B C edge q N Q budget tn hs ht same hp es badA badB ac bc selected
 have add:=SourceCoverage.qadd_le_add localBill (Rat.le_refl (a:=
  (geometric Rule5ActualTrace.base*forestCoefficient N Q*(4*Rule5ActualTrace.base^(-4:Int)))*Rule5ActualTrace.base^q))
 have regroup:geometric Rule5ActualTrace.base*forestCoefficient N Q*(4*Rule5ActualTrace.base^(-4:Int))=
  (400000000/417428121:Rat)*forestCoefficient N Q := by
  rw [Rat.mul_assoc,Rat.mul_comm (forestCoefficient N Q) (4*Rule5ActualTrace.base^(-4:Int)),←Rat.mul_assoc,badPair_forest_constant]
 rw [regroup] at add forest
 exact Rat.le_trans forest (by simpa only [badPairSourcePolynomial,Rat.add_mul] using add)

/-- Arbitrary callback work is kept literally in the source split. No handler
fee, callback output bound, or below-work induction hypothesis is assumed. -/
theorem badPairSource_complete_split_bound (actual : GenericForest.FrontierWork.Ordinary)
 (W : OrdinaryWork) (T S : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex×RMAF.Vertex) (q N Q : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (budget:q≤Q)
 (hs:(leaves S).Nodup) (ht:(leaves T).Nodup) (same:∀x,x∈leaves T↔x∈leaves S)
 (hp:partitionCheck (leaves S) [A,B,C]=true) (es:pairwiseEmbeddings S [A,B,C]=true)
 (badA:restrictionAgrees S T A=false) (badB:restrictionAgrees S T B=false)
 (ac:BinaryExchange.Disj T A C) (bc:BinaryExchange.Disj T B C)
 (selected:PairGeometry.choose T A B=some (.edge edge)) :
 (badPairSource actual W T S A B C edge q).value=Hard2Dispatcher.badPair actual T S A B C edge q ∧
 ((badPairSource actual W T S A B C edge q).work:Rat)≤
 badPairSourcePolynomial N Q*Rule5ActualTrace.base^q+
 (queryWork W (forestQueries actual (Hard2Dispatcher.badPair actual T S A B C edge q).calls):Rat) := by
 constructor
 · exact badPairSource_value actual W T S A B C edge q
 · rw [badPairSource_split,Rat.natCast_add]
   exact SourceCoverage.qadd_le_add
    (badPairSource_complete_semantic_bound actual T S A B C edge q N Q tn sn budget hs ht same hp es badA badB ac bc selected)
    (Rat.le_refl)
end OrdinaryDispatch.Hard2SourceWork
