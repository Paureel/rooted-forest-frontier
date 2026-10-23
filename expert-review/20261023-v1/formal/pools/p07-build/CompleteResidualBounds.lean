import CompleteNamedSources
namespace OrdinaryDispatch.CompleteSource
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.OuterSource
open OrdinaryDispatch.FastOrdinary Universal233.BothBad Universal233.Hard2Overlap Universal233.PaidAssembly
open GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork

def paidResidualDebit (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (c : CherryBranching.Candidate) (q : Nat) (out : Result) : Nat :=
 match (paidOuterMeter T S c out).value with
 | .bad X Y Z edge=>(badPairSource actual (fun _ _ _=>0) T S X Y Z edge q).work
 | _=>0

def routeResidualDebit (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (c : CherryBranching.Candidate) (q : Nat) : Hard2Route→Nat
 | .disjointPaid=>(disjointRunSource actual (fun _ _ _=>0) T S c.a c.b q).work
 | .paid out=>paidResidualDebit actual T S c q out
 | _=>0

theorem concrete_named_residual_split (T S : Tree) (c : CherryBranching.Candidate) (q : Nat)
 (route : Hard2Route) :
 namedRouteDebit (actualNamedFees (fun _ _ _=>0) (concreteResiduals (cutoff FastOrdinary.solve q) T S c q) T S c q) T S c route=
 namedRouteDebit (actualNamedFees (fun _ _ _=>0) ⟨0,fun _=>0⟩ T S c q) T S c route+
 routeResidualDebit (cutoff FastOrdinary.solve q) T S c q route := by
 cases route with
 | refused=>rfl
 | direct a=>rfl
 | admittedRule5=>simp [namedRouteDebit,actualNamedFees,routeResidualDebit]
 | disjointPaid=>simp [namedRouteDebit,actualNamedFees,routeResidualDebit,concreteResiduals,queryWork_zero]
 | paid out=>
   simp only [namedRouteDebit,actualNamedFees,routeResidualDebit,paidResidualDebit]
   cases r:(paidOuterMeter T S c out).value <;>
    simp [r,paidNamedDebit,paidBodyDebit,concreteResiduals,queryWork_zero]

theorem badPairSourcePolynomial_nonneg (N Q : Nat) : 0≤badPairSourcePolynomial N Q := by
 unfold badPairSourcePolynomial
 exact Rat.add_nonneg Rat.natCast_nonneg (Rat.mul_nonneg (by decide +kernel) Rat.natCast_nonneg)

theorem selected_paid_residual_bound (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree}
 {c : CherryBranching.Candidate} (q N Q : Nat) (out : Result)
 (proper0:DepthOne.proper T S=true) (hard:CherryBranching.select T S=some (.hard2,c))
 (selected:runHard2 T S c=some out) (tn:treeNodes T≤N) (sn:treeNodes S≤N) (budget:q≤Q) :
 (paidResidualDebit actual T S c q out:Rat)≤badPairSourcePolynomial N Q*Rule5ActualTrace.base^q := by
 have nn:0≤badPairSourcePolynomial N Q*Rule5ActualTrace.base^q:=
  Rat.mul_nonneg (badPairSourcePolynomial_nonneg N Q) (Rat.le_of_lt (Rat.pow_pos (by decide +kernel)))
 obtain ⟨p,r,cuts,hcuts,graph,hp,es,partEq⟩:=actual_source_inputs proper0 hard
 have basic:=OrdinaryPriorityBridge.proper_parts proper0
 have ht:=basic.1
 have hs:=basic.2.1
 have same:∀x,x∈leaves T↔x∈leaves S:=fun x=>basic.2.2.mem_iff
 have hl:∀x,x∈leaves S→x∈leaves T:=fun x hx=>(same x).2 hx
 have raw:Hard2Overlap.select T (leftParent S p) (rightParent S r) (rootParent S p r)=some out:=by
  simpa only [runHard2,cuts] using selected
 cases out with
 | disjoint=>simpa [paidResidualDebit,paidOuterMeter,cuts,hard2ParentsMeter_value] using nn
 | clique v=>simpa [paidResidualDebit,paidOuterMeter,cuts,hard2ParentsMeter_value] using nn
 | diagonal o v w=>simpa [paidResidualDebit,paidOuterMeter,cuts,hard2ParentsMeter_value] using nn
 | four o v w=>simpa [paidResidualDebit,paidOuterMeter,cuts,hard2ParentsMeter_value] using nn
 | pair o choice=>cases choice with
  | vertex v=>simpa [paidResidualDebit,paidOuterMeter,cuts,hard2ParentsMeter_value] using nn
  | edge edge=>
   let A:=first o (leftParent S p) (rightParent S r) (rootParent S p r)
   let B:=second o (leftParent S p) (rightParent S r) (rootParent S p r)
   let C:=third o (leftParent S p) (rightParent S r) (rootParent S p r)
   obtain ⟨pp,pe,ne,pairProper,chosen,valid,other⟩:=selected_pair_guards ht hl hp es raw
   have guards:=select_sound ht hl hp raw
   have ac:BinaryExchange.Disj T A C:=FreshPairReview.actual_clear_disj T _ _ guards.1
   have bc:BinaryExchange.Disj T B C:=FreshPairReview.actual_clear_disj T _ _ guards.2.1
   have shape:(paidOuterMeter T S c (.pair o (.edge edge))).value=
    (if restrictionAgrees S T A && restrictionAgrees S T B then PaidRoute.good A B C else
     if restrictionAgrees S T A || restrictionAgrees S T B then .hard else .bad A B C edge):=by
    simp only [paidOuterMeter,cuts,hard2ParentsMeter_value,meterRestrictionAgrees_value]
    split <;> rfl
   by_cases one:(restrictionAgrees S T A || restrictionAgrees S T B)=true
   · have zero:paidResidualDebit actual T S c q (.pair o (.edge edge))=0:=by
      unfold paidResidualDebit
      rw [shape]
      by_cases both:(restrictionAgrees S T A && restrictionAgrees S T B)=true
      · simp [both]
      · simp [both,one]
     rw [zero];exact nn
   · have ba:restrictionAgrees S T A=false:=by cases a:restrictionAgrees S T A <;> simp_all
     have bb:restrictionAgrees S T B=false:=by cases b:restrictionAgrees S T B <;> simp_all
     have binding:paidResidualDebit actual T S c q (.pair o (.edge edge))=
      (badPairSource actual (fun _ _ _=>0) T S A B C edge q).work:=by
      unfold paidResidualDebit
      rw [shape]
      simp [ba,bb]
     rw [binding]
     exact badPairSource_complete_semantic_bound actual T S A B C edge q N Q tn sn budget hs ht same pp pe ba bb ac bc chosen

theorem disjoint_route_facts (T S : Tree) (c : CherryBranching.Candidate) (q : Nat)
 (route:(hard2FrontMeter T S c q).value=.disjointPaid) :
 runHard2 T S c=some .disjoint ∧ (CherryBranching.pendantPartition S c.a c.b).all (restrictionAgrees T S)=false ∧
 ((CherryBranching.pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length≠2 := by
 cases hg:runHard2 T S c with
 | none=>simp [hard2FrontMeter,hg] at route
 | some out=>cases out with
  | disjoint=>
   simp only [hard2FrontMeter,runHard2Meter_value,hg,Rule5PendantLocalWork.partition_value,meterAll_value,meterRestrictionAgrees_value,meterFilter_value] at route
   split at route
   · contradiction
   · rename_i na
     split at route
     · contradiction
     · rename_i nt
       exact ⟨rfl,Bool.eq_false_iff.mpr na,nt⟩
  | clique v=>simp [hard2FrontMeter,hg] at route
  | diagonal o v w=>simp [hard2FrontMeter,hg] at route
  | four o v w=>simp [hard2FrontMeter,hg] at route
  | pair o choice=>simp [hard2FrontMeter,hg] at route

theorem paid_route_facts (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Result)
 (route:(hard2FrontMeter T S c q).value=.paid out) : runHard2 T S c=some out ∧ out≠.disjoint := by
 cases hg:runHard2 T S c with
 | none=>simp [hard2FrontMeter,hg] at route
 | some r=>cases r with
  | disjoint=>
   simp only [hard2FrontMeter,runHard2Meter_value,hg] at route
   split at route
   · contradiction
   · split at route <;> contradiction
  | clique v=>simp [hard2FrontMeter,hg] at route;cases route;exact ⟨rfl,by intro h;cases h⟩
  | diagonal o v w=>simp [hard2FrontMeter,hg] at route;cases route;exact ⟨rfl,by intro h;cases h⟩
  | four o v w=>simp [hard2FrontMeter,hg] at route;cases route;exact ⟨rfl,by intro h;cases h⟩
  | pair o choice=>simp [hard2FrontMeter,hg] at route;cases route;exact ⟨rfl,by intro h;cases h⟩

def disjointSourcePolynomial (N Q : Nat) : Rat:=
 (disjointRunPolynomial N:Rat)+geometric Rule5ActualTrace.base*forestCoefficient N Q*
 (2*Rule5ActualTrace.base^(-1:Int)+4*Rule5ActualTrace.base^(-4:Int))
def residualSourcePolynomial (N Q : Nat) : Rat:=disjointSourcePolynomial N Q+badPairSourcePolynomial N Q

theorem disjointSourcePolynomial_nonneg (N Q : Nat) : 0≤disjointSourcePolynomial N Q := by
 unfold disjointSourcePolynomial
 exact Rat.add_nonneg Rat.natCast_nonneg (Rat.mul_nonneg
  (Rat.mul_nonneg (geometric_properties _ (by decide +kernel)).2.2.1 Rat.natCast_nonneg)
  (Rat.add_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.zpow_pos (by decide +kernel))))
   (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.zpow_pos (by decide +kernel))))))

theorem selected_route_residual_bound (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree}
 {c : CherryBranching.Candidate} (q N Q : Nat)
 (proper0:DepthOne.proper T S=true) (hard:CherryBranching.select T S=some (.hard2,c))
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (budget:q≤Q) :
 (routeResidualDebit actual T S c q (hard2FrontMeter T S c q).value:Rat)≤
 residualSourcePolynomial N Q*Rule5ActualTrace.base^q := by
 have pow:0≤Rule5ActualTrace.base^q:=Rat.le_of_lt (Rat.pow_pos (by decide +kernel))
 have dn:=disjointSourcePolynomial_nonneg N Q
 have bn:=badPairSourcePolynomial_nonneg N Q
 have nn:0≤residualSourcePolynomial N Q*Rule5ActualTrace.base^q:=Rat.mul_nonneg (Rat.add_nonneg dn bn) pow
 cases route:(hard2FrontMeter T S c q).value with
 | refused=>exact nn
 | direct a=>exact nn
 | admittedRule5=>exact nn
 | disjointPaid=>
   have facts:=disjoint_route_facts T S c q route
   obtain ⟨p,r,cuts,hcuts,graph,hp,es,partEq⟩:=actual_source_inputs proper0 hard
   have blocks:=SourceCoverage.partitionCheck_block_bound _ _ hp
   have leavesN:=Nat.le_trans (leaves_nodes S) sn
   have three:3≤N:=by simp only [List.length_cons,List.length_nil] at blocks;omega
   have b:=disjointRunSource_bound actual T S c q N Q three budget tn sn proper0 hard facts.2.1 facts.2.2
   have extra:=Rat.mul_nonneg bn pow
   simpa only [routeResidualDebit,residualSourcePolynomial,disjointSourcePolynomial,Rat.add_mul] using
    (Rat.le_trans b (show disjointSourcePolynomial N Q*Rule5ActualTrace.base^q≤
     disjointSourcePolynomial N Q*Rule5ActualTrace.base^q+badPairSourcePolynomial N Q*Rule5ActualTrace.base^q by
      have h:disjointSourcePolynomial N Q*Rule5ActualTrace.base^q+0≤
       disjointSourcePolynomial N Q*Rule5ActualTrace.base^q+badPairSourcePolynomial N Q*Rule5ActualTrace.base^q:=Rat.add_le_add_left.mpr extra
      simpa only [Rat.add_zero] using h))
 | paid out=>
   have facts:=paid_route_facts T S c q out route
   have b:=selected_paid_residual_bound actual q N Q out proper0 hard facts.1 tn sn budget
   have extra:=Rat.mul_nonneg dn pow
   simpa only [routeResidualDebit,residualSourcePolynomial,Rat.add_mul] using
    (Rat.le_trans b (show badPairSourcePolynomial N Q*Rule5ActualTrace.base^q≤
     disjointSourcePolynomial N Q*Rule5ActualTrace.base^q+badPairSourcePolynomial N Q*Rule5ActualTrace.base^q by
      have h:0+badPairSourcePolynomial N Q*Rule5ActualTrace.base^q≤
       disjointSourcePolynomial N Q*Rule5ActualTrace.base^q+badPairSourcePolynomial N Q*Rule5ActualTrace.base^q:=Rat.add_le_add_right.mpr extra
      simpa only [Rat.zero_add] using h))
end OrdinaryDispatch.CompleteSource
