import JoinPrecontrols
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.WorkIntegration
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion
open LocalDispatchEnvelope

/-- Bound the actual, duplicate-preserving descendant construction, at the
selected child address. No descendant-size hypothesis is supplied by a caller. -/
theorem badPair_selected_descendant_caps (T : Tree) (A B : List Nat)
 (edge : RMAF.Vertex×RMAF.Vertex) (N : Nat) (tn:treeNodes T≤N)
 (selected:PairGeometry.choose T A B=some (.edge edge)) :
 (pairDescendantsMeter T edge.2).value.length≤N ∧
 (pairDescendantsMeter T edge.2).work≤56*(N+1)^3 := by
 have chosen:=PairGeometry.choose_sound T A B (.edge edge) selected
 have address:=Nat.le_trans (pairEdges_address T edge chosen.2.1).2 tn
 exact ⟨Nat.le_trans (pairDescendantsMeter_length T edge.2) (Nat.le_trans (leaves_nodes T) tn),
  pairDescendantsMeter_bound T edge.2 N tn address⟩

def localBadPairCoefficient (N Q : Nat) :=
 plannerExecutionCoefficient N Q+56*(N+1)^3+128*(N+1)^2+22

/-- All true-branch source counters: descendant construction, original planner,
local execution, C restriction guard, and both literal wrappers. -/
theorem badPairLocalSource_local_bound (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q N Q : Nat)
 (three:3≤N) (tn:treeNodes T≤N) (sn:treeNodes S≤N) (budget:q≤Q)
 (hs:(leaves S).Nodup) (hp:partitionCheck (leaves S) [A,B,C]=true)
 (selected:PairGeometry.choose T A B=some (.edge edge))
 (goodC:restrictionAgrees S T C=true) :
 (badPairLocalSource actual T S A B C edge q).work≤localBadPairCoefficient N Q*2^(q+1) := by
 have caps:=semantic_partition_caps S A B C N hs sn hp
 have d:=badPair_selected_descendant_caps T A B edge N tn selected
 have pe:=planner_execution_bound actual S T A B C (pairDescendantsMeter T edge.2).value q N Q
  three tn sn caps.1 caps.2.1 caps.2.2 d.1 budget
 have guard:=meterRestrictionAgrees_bound S T C N (by omega) (by omega) caps.2.2
 have pos:1≤2^(q+1):=Nat.two_pow_pos _
 have lift:=Nat.mul_le_mul_left (56*(N+1)^3+128*(N+1)^2+22) pos
 simp only [Nat.mul_one,Nat.add_mul] at lift
 simp only [badPairLocalSource,meterRestrictionAgrees_value,goodC,ite_true,
  bothBadLocalPairLocalSource,localBadPairCoefficient,Nat.add_mul]
 omega

def localBadPairPolynomial (N Q : Nat) := 2*localBadPairCoefficient N Q+6

theorem badPairLocalSource_local_semantic_bound (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q N Q : Nat)
 (three:3≤N) (tn:treeNodes T≤N) (sn:treeNodes S≤N) (budget:q≤Q)
 (hs:(leaves S).Nodup) (hp:partitionCheck (leaves S) [A,B,C]=true)
 (selected:PairGeometry.choose T A B=some (.edge edge))
 (goodC:restrictionAgrees S T C=true) :
 ((badPairLocalSource actual T S A B C edge q).work:Rat)≤
 (localBadPairPolynomial N Q:Rat)*Rule5ActualTrace.base^q := by
 have h:=badPairLocalSource_local_bound actual T S A B C edge q N Q three tn sn budget hs hp selected goodC
 exact Rat.le_trans (Rat.natCast_le_natCast.2 (Nat.le_trans h (Nat.le_add_right _ 6)))
  (binary_prefix_absorb (localBadPairCoefficient N Q) q)

def badPairLocalPolynomial (N Q : Nat) := localBadPairPolynomial N Q+groupedBadPairPolynomial N Q

/-- Complete unchanged local source envelope, at original q. Both actual guard
branches are proved; callback/forest work remains in the exact source split. -/
theorem badPairLocalSource_semantic_bound (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q N Q : Nat)
 (three:3≤N) (tn:treeNodes T≤N) (sn:treeNodes S≤N) (budget:q≤Q)
 (hs:(leaves S).Nodup) (hp:partitionCheck (leaves S) [A,B,C]=true)
 (selected:PairGeometry.choose T A B=some (.edge edge)) :
 ((badPairLocalSource actual T S A B C edge q).work:Rat)≤
 (badPairLocalPolynomial N Q:Rat)*Rule5ActualTrace.base^q := by
 have pos:0≤Rule5ActualTrace.base^q:=Rat.le_of_lt (Rat.pow_pos (by decide +kernel))
 cases hc:restrictionAgrees S T C with
 | false=>
  have h:=badPairLocalSource_grouped_semantic_bound actual T S A B C edge q N Q tn sn budget hs hp selected hc
  have c:groupedBadPairPolynomial N Q≤badPairLocalPolynomial N Q:=by
   simp only [badPairLocalPolynomial];omega
  exact Rat.le_trans h (Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.2 c) pos)
 | true=>
  have h:=badPairLocalSource_local_semantic_bound actual T S A B C edge q N Q three tn sn budget hs hp selected hc
  have c:localBadPairPolynomial N Q≤badPairLocalPolynomial N Q:=by
   simp only [badPairLocalPolynomial];omega
  exact Rat.le_trans h (Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.2 c) pos)
end OrdinaryDispatch.Hard2SourceWork
