import GroupedPairWeighted
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork GenericForest GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open OrdinaryDispatch.WorkIntegration OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion

theorem badPair_semantic_sizes (T S : Tree) (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex)
 (N : Nat) (tn:treeNodes T≤N) (sn:treeNodes S≤N) (ns:(leaves S).Nodup)
 (hp:partitionCheck (leaves S) [A,B,C]=true)
 (selected:PairGeometry.choose T A B=some (.edge edge)) :
 A.length≤N ∧ B.length≤N ∧ C.length≤N ∧ edge.2.length≤N:=by
 have flat:=(FinalCutRecovery.checked_flatten_perm S [A,B,C] ns hp).length_eq
 have cells:([A,B,C].flatten).length≤N:=by have l:=leaves_nodes S;omega
 have aa:=block_cells [A,B,C] A (by simp)
 have bb:=block_cells [A,B,C] B (by simp)
 have cc:=block_cells [A,B,C] C (by simp)
 have chosen:=PairGeometry.choose_sound T A B (.edge edge) selected
 have address:edge.2.length≤N:=Nat.le_trans (pairEdges_address T edge chosen.2.1).2 tn
 exact ⟨by omega,by omega,by omega,address⟩

def groupedBadPairPolynomial (N Q : Nat):=2*groupedBadPairCoefficient N Q+6

theorem badPairLocalSource_grouped_semantic_bound (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q N Q : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (budget:q≤Q) (ns:(leaves S).Nodup)
 (hp:partitionCheck (leaves S) [A,B,C]=true)
 (selected:PairGeometry.choose T A B=some (.edge edge)) (badC:restrictionAgrees S T C=false) :
 ((badPairLocalSource actual T S A B C edge q).work:Rat)≤
 (groupedBadPairPolynomial N Q:Rat)*Rule5ActualTrace.base^q:=by
 have sizes:=badPair_semantic_sizes T S A B C edge N tn sn ns hp selected
 have natbound:=badPairLocalSource_grouped_bound actual T S A B C edge q N Q tn sn sizes.1 sizes.2.1 sizes.2.2.1 ns sizes.2.2.2 budget badC
 have lift:(badPairLocalSource actual T S A B C edge q).work≤groupedBadPairCoefficient N Q*2^(q+1)+6:=by omega
 exact Rat.le_trans (Rat.natCast_le_natCast.2 lift) (binary_prefix_absorb _ q)

/-- Complete zero-callback source envelope for the actual grouped branch.
The local-mode branch remains a separate named dependency. -/
theorem badPairSource_grouped_semantic_bound (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q N Q : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (budget:q≤Q)
 (hs:(leaves S).Nodup) (ht:(leaves T).Nodup) (same:∀x,x∈leaves T↔x∈leaves S)
 (hp:partitionCheck (leaves S) [A,B,C]=true) (es:pairwiseEmbeddings S [A,B,C]=true)
 (badA:restrictionAgrees S T A=false) (badB:restrictionAgrees S T B=false) (badC:restrictionAgrees S T C=false)
 (ac:BinaryExchange.Disj T A C) (bc:BinaryExchange.Disj T B C)
 (selected:PairGeometry.choose T A B=some (.edge edge)) :
 ((badPairSource actual (fun _ _ _=>0) T S A B C edge q).work:Rat)≤
 ((groupedBadPairPolynomial N Q:Rat)+geometric Rule5ActualTrace.base*forestCoefficient N Q*(4*Rule5ActualTrace.base^(-4:Int)))*Rule5ActualTrace.base^q:=by
 have localBill:=badPairLocalSource_grouped_semantic_bound actual T S A B C edge q N Q tn sn budget hs hp selected badC
 have forest:=badPairSource_semantic_forest_bound actual T S A B C edge q N Q budget tn hs ht same hp es badA badB ac bc selected
 have add:=SourceCoverage.qadd_le_add localBill (Rat.le_refl (a:=
  (geometric Rule5ActualTrace.base*forestCoefficient N Q*(4*Rule5ActualTrace.base^(-4:Int)))*Rule5ActualTrace.base^q))
 exact Rat.le_trans forest (by simpa only [Rat.add_mul] using add)
end OrdinaryDispatch.Hard2SourceWork
