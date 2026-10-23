import DisjointParentBound
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork SourceCoverage
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open Universal233.BothBad Universal233.PaidQueries Universal233.CherryBranching
open Universal233.Rule5SelectedLocalWork Universal233.Rule5PendantLocalWork
open Universal233.Hard2Overlap Universal233.PaidAssembly
open OrdinaryDispatch.WorkIntegration OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion

theorem callsForestDebit_append (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (xs ys : List Call) :
 callsForestDebit actual W (xs++ys)=callsForestDebit actual W xs+callsForestDebit actual W ys:=by
 simp only [callsForestDebit,List.map_append,List.sum_append]

theorem childForestDebit_as_calls (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T : Tree) (q : Nat) (cs : List Child) :
 childForestDebit actual W T q cs=callsForestDebit actual W
  (cs.filterMap (fun c=>(remaining q c).map (fun b=>(⟨some T,c.sourceForest,b⟩:Call)))):=by
 induction cs with
 | nil=>rfl
 | cons c cs ih=>
   cases h:remaining q c with
   | none=>simpa only [childForestDebit,Rule5OrdinaryDispatch.forestJobs,Rule5OrdinaryDispatch.jobFor,
     List.filterMap_cons,h,Option.map_none,callsForestDebit] using ih
   | some b=>
     simpa only [childForestDebit,Rule5OrdinaryDispatch.forestJobs,Rule5OrdinaryDispatch.jobFor,
      List.filterMap_cons,h,Option.map_some,callsForestDebit,List.map_cons,List.sum_cons] using
      congrArg (fun n=>OrdinaryDispatch.WorkRecursion.forestWork actual W (some T) c.sourceForest b+n) ih

theorem selected_pendant_caps (T S : Tree) (c : Candidate) (N : Nat) (sn:treeNodes S≤N)
 (proper0:DepthOne.proper T S=true) (hard:CherryBranching.select T S=some (.hard2,c)) :
 (pendantPartition S c.a c.b).length=3 ∧ ∀U,U∈pendantPartition S c.a c.b→U.length≤N:=by
 obtain ⟨p,r,_,_,_,_,_,partEq⟩:=actual_source_inputs proper0 hard
 have a:(PaidAssembly.leftParent S p).length≤N:=by
  simpa only [PaidAssembly.leftParent,subtree_labels_value] using
   Nat.le_trans (subtree_labels_payload S p).1 (Nat.le_trans (leaves_nodes S) sn)
 have b:(PaidAssembly.rightParent S r).length≤N:=by
  simpa only [PaidAssembly.rightParent,subtree_labels_value] using
   Nat.le_trans (subtree_labels_payload S r).1 (Nat.le_trans (leaves_nodes S) sn)
 have d:(PaidAssembly.rootParent S p r).length≤N:=Nat.le_trans (List.length_filter_le _ _) (Nat.le_trans (leaves_nodes S) sn)
 rw [partEq]
 constructor
 · rfl
 · intro U hm
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
   rcases hm with rfl|rfl|rfl <;> assumption

def disjointRunPolynomial (N : Nat):=
 2*singletonChildBudget N+partitionBudget N+2*(agreementK N+3*N+16)+
 disjointQueryPolynomial N 3+2*N+32

theorem disjointRunSource_local (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (c : Candidate) (q N : Nat) (three:3≤N)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N)
 (proper0:DepthOne.proper T S=true) (hard:CherryBranching.select T S=some (.hard2,c)) :
 (disjointRunSource actual (fun _ _ _=>0) T S c.a c.b q).work≤
 disjointRunPolynomial N+callsForestDebit actual (fun _ _ _=>0)
  (Hard2Trace.disjointExecution actual T S c.a c.b q).calls:=by
 have caps:=selected_pendant_caps T S c N sn proper0 hard
 have tl:=Nat.le_trans (leaves_nodes T) tn
 have sl:=Nat.le_trans (leaves_nodes S) sn
 have buildX:=singleton_child_work S c.a
 have buildY:=singleton_child_work S c.b
 have buildP:=partition_work S c.a c.b
 have monoX:singletonChildBudget (leaves S).length≤singletonChildBudget N:=by
  unfold singletonChildBudget singletonPartitionBudget
  repeat first | exact sl | exact Nat.le_refl _ | apply Nat.add_le_add | apply Nat.mul_le_mul
 have monoP:partitionBudget (leaves S).length≤partitionBudget N:=by
  unfold partitionBudget coreBudget pendantPayloadBudget blocksBudget payloadCap cutsBudget cutGuardBudget minimalBudget
  repeat first | exact sl | exact Nat.le_refl _ | apply Nat.add_le_add | apply Nat.mul_le_mul
 have kmono:agreementK (leaves T).length≤agreementK N:=(simpleBudget_mono tl).2.2
 have child:=ordinary_run_children_local actual (fun _=>0) T S q [singletonChild S c.a,singletonChild S c.b] proper0
 simp only [List.length_cons,List.length_nil] at child
 have childBound:(runChildrenMeter actual (fun _=>0) (fun F=>(agreementMeter T S F).work) T S q
  [singletonChild S c.a,singletonChild S c.b]).localWork≤2*(agreementK N+3*N+16)+4:=by omega
 have query:=disjointQueryLocalSource_bound actual T S (pendantPartition S c.a c.b) q N three tn sn caps.2
 rw [caps.1] at query
 have best:=chooseMeter_bound
  (OrdinaryDispatch.runChildren actual T S q [singletonChild S c.a,singletonChild S c.b])
  (OrdinaryDispatch.DisjointParents.query actual T S (pendantPartition S c.a c.b) q).answer N
  (by intro F ans
      have ok:=(OrdinaryDispatch.runChildren_sound actual T S q _ F ans).1
      have part:partitionCheck (leaves T) F=true:=by simp only [agreement,Bool.and_eq_true] at ok;exact ok.1.1.1.1
      exact Nat.le_trans (partitionCheck_block_bound _ _ part) tl)
  (by intro F ans
      have ok:=(OrdinaryDispatch.DisjointParents.query_sound actual T S _ F q ans).1
      have part:partitionCheck (leaves T) F=true:=by simp only [agreement,Bool.and_eq_true] at ok;exact ok.1.1.1.1
      exact Nat.le_trans (partitionCheck_block_bound _ _ part) tl)
 have debit:=childForestDebit_as_calls actual (fun _ _ _=>0) T q [singletonChild S c.a,singletonChild S c.b]
 change childForestDebit actual (fun _ _ _=>0) T q [singletonChild S c.a,singletonChild S c.b]=
  callsForestDebit actual (fun _ _ _=>0) (Hard2Combine.unitCalls S T c.a c.b q) at debit
 simp only [Hard2Trace.disjointExecution,Hard2Combine.combine,callsForestDebit_append]
 simp only [disjointRunSource,singleton_child_value,partition_value,runChildrenSource,
 ordinary_run_children_value,disjointQuerySource,disjointQueryLocalSource_value,disjointRunPolynomial]
 omega

theorem disjointRunSource_bound (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (c : Candidate) (q N Q : Nat) (three:3≤N) (budget:q≤Q)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N)
 (proper0:DepthOne.proper T S=true) (hard:CherryBranching.select T S=some (.hard2,c))
 (notAll:(pendantPartition S c.a c.b).all (restrictionAgrees T S)=false)
 (notTwo:((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length≠2) :
 ((disjointRunSource actual (fun _ _ _=>0) T S c.a c.b q).work:Rat)≤
 ((disjointRunPolynomial N:Rat)+geometric Rule5ActualTrace.base*forestCoefficient N Q*
 (2*Rule5ActualTrace.base^(-1:Int)+4*Rule5ActualTrace.base^(-4:Int)))*Rule5ActualTrace.base^q:=by
 have localBill:=disjointRunSource_local actual T S c q N three tn sn proper0 hard
 have debit:=callsForestDebit_weighted actual (Hard2Trace.disjointExecution actual T S c.a c.b q).calls q N Q budget
  (disjoint_queries_proper actual q proper0 hard)
  (by intro a hm;exact Nat.le_trans (Hard2Size.disjoint_target_bound actual T S c.a c.b q a hm).2 (Nat.le_trans (leaves_nodes T) tn))
  (by intro a hm;exact Nat.le_of_lt (Hard2Trace.disjointExecution_strict actual q proper0 hard a hm))
 have mass:=Hard2Trace.disjointExecution_mass actual q proper0 hard notAll notTwo Rule5ActualTrace.base (by decide +kernel) (by decide +kernel)
 have positive:0≤geometric Rule5ActualTrace.base*forestCoefficient N Q*Rule5ActualTrace.base^q:=
  Rat.mul_nonneg (Rat.mul_nonneg (geometric_properties _ (by decide +kernel)).2.2.1 Rat.natCast_nonneg)
   (Rat.le_of_lt (Rat.pow_pos (by decide +kernel)))
 have weighted:=Rat.le_trans debit (Rat.mul_le_mul_of_nonneg_left mass positive)
 have localPow:=Rat.mul_le_mul_of_nonneg_left (call_base_pow_ge_one q)
  (show 0≤(disjointRunPolynomial N:Rat) from Rat.natCast_nonneg)
 rw [Rat.mul_one] at localPow
 have total:=Rat.le_trans (Rat.natCast_le_natCast.2 localBill)
  (by simpa only [Rat.natCast_add] using qadd_le_add localPow weighted)
 have regroup (x : Rat):(geometric Rule5ActualTrace.base*forestCoefficient N Q*Rule5ActualTrace.base^q)*x=
  (geometric Rule5ActualTrace.base*forestCoefficient N Q*x)*Rule5ActualTrace.base^q:=by
  rw [Rat.mul_assoc,Rat.mul_comm (Rule5ActualTrace.base^q) x,←Rat.mul_assoc]
 simpa only [regroup,Rat.add_mul] using total
end OrdinaryDispatch.Hard2SourceWork
