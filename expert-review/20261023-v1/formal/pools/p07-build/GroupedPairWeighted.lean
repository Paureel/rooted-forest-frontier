import GroupedPairBound
import BadPairForestBound
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open OrdinaryDispatch.WorkIntegration OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion

def groupedMaterialCoefficient (N Q : Nat):=groupedPairCoefficient N Q+148

theorem groupPair_local_and_calls_bound (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q N Q : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (al:A.length≤N) (bl:B.length≤N) (cl:C.length≤N)
 (ns:(leaves S).Nodup) (address:edge.2.length≤N) (budget:q≤Q) :
 (groupPairLocalSource actual T S A B C edge q).work+
 12*(groupPairLocalSource actual T S A B C edge q).value.queries.length+4≤groupedMaterialCoefficient N Q*2^(q+1):=by
 have body:=groupPairLocalSource_bound actual T S A B C edge q N Q tn sn al bl cl ns address budget
 have trace:=Nat.mul_le_mul_left 12 body.2
 have pos:1≤2^(q+1):=Nat.two_pow_pos _
 simp only [groupedMaterialCoefficient,Nat.add_mul,Nat.mul_assoc] at trace ⊢
 omega

theorem groupPair_local_and_calls_weighted (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q N Q : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (al:A.length≤N) (bl:B.length≤N) (cl:C.length≤N)
 (ns:(leaves S).Nodup) (address:edge.2.length≤N) (budget:q≤Q) :
 (( (groupPairLocalSource actual T S A B C edge q).work+
 12*(groupPairLocalSource actual T S A B C edge q).value.queries.length+4:Nat):Rat)≤
 ((2*groupedMaterialCoefficient N Q+6:Nat):Rat)*Rule5ActualTrace.base^q:=by
 have natbound:=groupPair_local_and_calls_bound actual T S A B C edge q N Q tn sn al bl cl ns address budget
 have lift:((groupPairLocalSource actual T S A B C edge q).work+
 12*(groupPairLocalSource actual T S A B C edge q).value.queries.length+4)≤groupedMaterialCoefficient N Q*2^(q+1)+6:=by omega
 exact Rat.le_trans (Rat.natCast_le_natCast.2 lift) (binary_prefix_absorb _ q)

def groupedBadPairCoefficient (N Q : Nat):=groupedMaterialCoefficient N Q+128*(N+1)^2+8

/-- The actual final dispatcher grouped branch, including the original C
restriction check and materialization of every literal group call. -/
theorem badPairLocalSource_grouped_bound (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q N Q : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (al:A.length≤N) (bl:B.length≤N) (cl:C.length≤N)
 (ns:(leaves S).Nodup) (address:edge.2.length≤N) (budget:q≤Q)
 (badC:restrictionAgrees S T C=false) :
 (badPairLocalSource actual T S A B C edge q).work≤groupedBadPairCoefficient N Q*2^(q+1):=by
 have localBill:=groupPair_local_and_calls_bound actual T S A B C edge q N Q tn sn al bl cl ns address budget
 have guard:=meterRestrictionAgrees_bound S T C N (by omega) (by omega) cl
 have pos:1≤2^(q+1):=Nat.two_pow_pos _
 have lift:=Nat.mul_le_mul_left (128*(N+1)^2+8) pos
 simp only [Nat.mul_one,Nat.add_mul] at lift
 simp only [badPairLocalSource,meterRestrictionAgrees_value,badC,Bool.false_eq_true,ite_false,groupedBadPairCoefficient,Nat.add_mul]
 omega
end OrdinaryDispatch.Hard2SourceWork
