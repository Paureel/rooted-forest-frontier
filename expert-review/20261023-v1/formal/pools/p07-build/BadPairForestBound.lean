import BadPairSource
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open Universal233.BothBad Universal233.PaidQueries
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion

theorem badPairSource_calls_drop (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat)
 (hs:(leaves S).Nodup) (ht:(leaves T).Nodup) (same:∀x,x∈leaves T↔x∈leaves S)
 (hp:partitionCheck (leaves S) [A,B,C]=true) (es:pairwiseEmbeddings S [A,B,C]=true)
 (badA:restrictionAgrees S T A=false) (badB:restrictionAgrees S T B=false)
 (ac:BinaryExchange.Disj T A C) (bc:BinaryExchange.Disj T B C)
 (selected:PairGeometry.choose T A B=some (.edge edge))
 (a : Call) (mem:a∈(Hard2Dispatcher.badPair actual T S A B C edge q).calls) : a.budget+2≤q:=by
 have bound:=Hard2Dispatcher.badPair_mass actual T S A B C edge q hs ht same hp es badA badB ac bc selected
  (2:Rat) (by decide) (by decide)
 have upper:(4:Rat)*2^(-4:Int)=1/4:=by cbv
 rw [upper] at bound
 have term:=Hard2Trace.trace_member_bound (2:Rat) (by decide) q _ a mem
 have low:=Rat.le_trans term bound
 have loss:2≤q-a.budget:=by
  by_cases yes:2≤q-a.budget
  · exact yes
  · exfalso
    have no:=yes
    have cases:q-a.budget=0 ∨ q-a.budget=1:=by omega
    rcases cases with d|d
    · rw [d] at low
      have one:(2:Rat)^(-((0:Nat):Int))=1:=by cbv
      rw [one] at low
      have bad:¬(1:Rat)≤1/4:=by cbv
      exact bad low
    · rw [d] at low
      have half:(2:Rat)^(-((1:Nat):Int))=1/2:=by cbv
      rw [half] at low
      have bad:¬(1/2:Rat)≤1/4:=by cbv
      exact bad low
 omega

/-- Forest overhead is now closed from the actual semantic source domain.
The remaining concrete local-work polynomial is displayed explicitly. -/
theorem badPairSource_semantic_forest_bound (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q N Q : Nat) (budget:q≤Q) (tn:treeNodes T≤N)
 (hs:(leaves S).Nodup) (ht:(leaves T).Nodup) (same:∀x,x∈leaves T↔x∈leaves S)
 (hp:partitionCheck (leaves S) [A,B,C]=true) (es:pairwiseEmbeddings S [A,B,C]=true)
 (badA:restrictionAgrees S T A=false) (badB:restrictionAgrees S T B=false)
 (ac:BinaryExchange.Disj T A C) (bc:BinaryExchange.Disj T B C)
 (selected:PairGeometry.choose T A B=some (.edge edge)) :
 ((badPairSource actual (fun _ _ _=>0) T S A B C edge q).work:Rat)≤
 ((badPairLocalSource actual T S A B C edge q).work:Rat)+
 (geometric Rule5ActualTrace.base*forestCoefficient N Q*(4*Rule5ActualTrace.base^(-4:Int)))*Rule5ActualTrace.base^q:=by
 have debit:=badPairSource_weighted_forest_debit actual T S A B C edge q N Q budget
  (badPair_query_proper actual T S A B C edge q hs ht same hp es selected)
  (by intro a hm;exact Nat.le_trans (Hard2Size.bad_pair_target_bound actual T S A B C edge q a hm).2 (Nat.le_trans (leaves_nodes T) tn))
  (by intro a hm;have drop:=badPairSource_calls_drop actual T S A B C edge q hs ht same hp es badA badB ac bc selected a hm;omega)
 have mass:=Hard2Dispatcher.badPair_mass actual T S A B C edge q hs ht same hp es badA badB ac bc selected
  Rule5ActualTrace.base (by decide +kernel) (by decide +kernel)
 have positive:0≤geometric Rule5ActualTrace.base*forestCoefficient N Q*Rule5ActualTrace.base^q:=
  Rat.mul_nonneg (Rat.mul_nonneg (geometric_properties _ (by decide +kernel)).2.2.1 Rat.natCast_nonneg)
   (Rat.le_of_lt (Rat.pow_pos (by decide +kernel)))
 have weighted:=Rat.mul_le_mul_of_nonneg_left mass positive
 have regroup (x : Rat):(geometric Rule5ActualTrace.base*forestCoefficient N Q*Rule5ActualTrace.base^q)*x=
  (geometric Rule5ActualTrace.base*forestCoefficient N Q*x)*Rule5ActualTrace.base^q:=by
  rw [Rat.mul_assoc,Rat.mul_comm (Rule5ActualTrace.base^q) x,←Rat.mul_assoc]
 have weighted':
  (geometric Rule5ActualTrace.base*forestCoefficient N Q*Rule5ActualTrace.base^q)*
   traceMass Rule5ActualTrace.base q (Hard2Dispatcher.badPair actual T S A B C edge q).calls≤
  (geometric Rule5ActualTrace.base*forestCoefficient N Q*(4*Rule5ActualTrace.base^(-4:Int)))*Rule5ActualTrace.base^q:=by
  calc
   _≤(geometric Rule5ActualTrace.base*forestCoefficient N Q*Rule5ActualTrace.base^q)*(4*Rule5ActualTrace.base^(-4:Int)):=weighted
   _=_:=regroup _
 have localRefl:((badPairLocalSource actual T S A B C edge q).work:Rat)≤
  ((badPairLocalSource actual T S A B C edge q).work:Rat):=Rat.le_refl
 exact Rat.le_trans debit (SourceCoverage.qadd_le_add localRefl weighted')
end OrdinaryDispatch.Hard2SourceWork
