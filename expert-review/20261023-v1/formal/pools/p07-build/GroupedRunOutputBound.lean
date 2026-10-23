import GroupedJobsBound
import LiteralReceiptSourceBound
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState ForestGroups Universal233 WholeSourceWork CoreWork
open GenericForest GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open Universal233.GroupedFullQuery Universal233.PaidQueries Universal233.Rule5SelectedLocalWork

theorem groupJobsFor_caps (T S : Tree) (A B C : List Nat) (o : CoreProgram.Output) (N : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (pl:o.partition.length≤N)
 (js : List (Job Problem (List (List Nat)))) (hj:BothBadGrouped.jobsFor T S A B C o=some js) :
 js.length=2 ∧ ∀p,.hard p∈js→targetNodes p.target≤N ∧ p.sources.length≤N:=by
 have prep:prepare (groupProblems (some T) (OutputState.sourceForest S o.partition) [A++B,C])=some js:=hj
 have spec:=prepare_spec _ js prep
 have len:=congrArg List.length spec.1
 simp only [List.length_map,groupProblems,List.length_cons,List.length_nil] at len
 refine ⟨len,?_⟩
 intro p hp
 have mem:p∈groupProblems (some T) (OutputState.sourceForest S o.partition) [A++B,C]:=by
  rw [←spec.1]
  exact List.mem_map.2 ⟨.hard p,hp,rfl⟩
 simp only [groupProblems,List.mem_map] at mem
 obtain ⟨U,_,eq⟩:=mem
 subst p
 have t:=localTarget_nodes_cap T U N tn
 have s:=owned_source_forest_caps S o.partition U N sn
 exact ⟨t,Nat.le_trans s.1 pl⟩

theorem groupCallbackMeter_bound (actual : GenericForest.FrontierWork.Ordinary) (p : Problem) (b N : Nat)
 (tn:targetNodes p.target≤N) (sl:p.sources.length≤N) :
 (groupCallbackMeter actual p b).work≤2*N+16:=by
 simp only [groupCallbackMeter]
 cases h:GenericForest.solve actual p.target p.sources b with
 | none=>simp only [];omega
 | some F=>
   have payload:=state_payload_forest_return actual p.target p.sources b F h
   have cap:=Nat.le_trans (labels_nodes p.target) tn
   simp only [StatePayloadSize] at payload
   simp only [additionalCostMeter];omega

def groupRunOutputPolynomial (N : Nat):=2*N+groupJobsForPolynomial N+384+2*(2*N+16)+20

theorem groupRunOutputLocalSource_bound (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (A B C : List Nat) (q : Nat) (o : CoreProgram.Output) (N : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (al:A.length≤N) (bl:B.length≤N) (cl:C.length≤N)
 (cut:o.sourceCuts.length≤N) (pl:o.partition.length≤N) (blocks:∀U,U∈o.partition→U.length≤N) :
 (groupRunOutputLocalSource actual T S A B C q o).work≤groupRunOutputPolynomial N:=by
 have jobs:=groupJobsForMeter_bound T S A B C o N tn sn al bl cl pl blocks
 simp only [groupRunOutputLocalSource]
 split
 · cases hj:(groupJobsForMeter T S A B C o).value with
   | none=>simp only [groupRunOutputPolynomial];omega
   | some js=>
     have j:BothBadGrouped.jobsFor T S A B C o=some js:=by simpa only [groupJobsForMeter_value] using hj
     have caps:=groupJobsFor_caps T S A B C o N tn sn pl js j
     have loc:=literalScheduleSource_local_bound (groupCallbackMeter actual) (q-o.sourceCuts.length) js
     rw [caps.1] at loc
     let r:=literalScheduleSource (groupCallbackMeter actual) (q-o.sourceCuts.length) js
     have origin (pb : Problem×Nat) (hm:pb∈r.value.queries):targetNodes pb.1.target≤N ∧ pb.1.sources.length≤N:=by
      have hard:=(literalScheduleSource_query_origin (groupCallbackMeter actual) _ js pb hm).1
      exact caps.2 pb.1 hard
     have cb:=GenericForest.LocalPolynomial.nat_sum_le_constant r.value.queries
       (fun pb=>(groupCallbackMeter actual pb.1 pb.2).work) (2*N+16)
       (by intro pb hm;have a:=origin pb hm;exact groupCallbackMeter_bound actual pb.1 pb.2 N a.1 a.2)
     have len:r.value.queries.length≤2:=by
      rw [literalScheduleSource_queries]
      exact Nat.le_trans (scheduleSourceMeter_queries_bound _ _ js) (by omega)
     have mul:=Nat.mul_le_mul_right (2*N+16) len
     have split:=literalScheduleSource_callback_split (groupCallbackMeter actual) (q-o.sourceCuts.length) js
     change r.callbackWork=_ at split
     have cbcap:r.callbackWork≤2*(2*N+16):=by
      rw [split]
      exact Nat.le_trans cb mul
     change r.localWork≤_ at loc
     change 2*o.sourceCuts.length+(groupJobsForMeter T S A B C o).work+r.localWork+r.callbackWork+20≤groupRunOutputPolynomial N
     unfold groupRunOutputPolynomial
     omega
 · simp only [groupRunOutputPolynomial];omega
end OrdinaryDispatch.Hard2SourceWork
