import GroupedOutputPayload
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState ForestGroups Universal233 WholeSourceWork CoreWork
open GenericForest GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open Universal233.GroupedFullQuery Universal233.PaidQueries Universal233.Rule5SelectedLocalWork

theorem groupedJobsFor_schedule_payload (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (A B C : List Nat) (o : CoreProgram.Output) (js : List (Job Problem (List (List Nat))))
 (hj:BothBadGrouped.jobsFor T S A B C o=some js) (N b : Nat) (tn:treeNodes T≤N)
 (xs : List (Nat×List (List Nat)))
 (h:(literalScheduleSource (groupCallbackMeter actual) b js).value.value.answers=some xs) :
 xs.length=2 ∧ ∀x,x∈xs→x.2.length≤N ∧ x.2.flatten.length≤N:=by
 have prep:prepare (groupProblems (some T) (OutputState.sourceForest S o.partition) [A++B,C])=some js:=hj
 have cap:=groupedSchedule_payload actual _ js prep N b (by
  intro p hm
  simp only [groupProblems,List.mem_map] at hm
  obtain ⟨U,_,eq⟩:=hm
  subst p
  exact localTarget_nodes_cap T U N tn) xs h
 simpa only [groupProblems,List.length_map,List.length_cons,List.length_nil] using cap

/-- All result cases are metered. A scheduled answer is flattened from the
literal two-job original receipt, including resolved and callback payloads. -/
theorem groupRunOutput_answer_bounds (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (A B C : List Nat) (q : Nat) (o : CoreProgram.Output) (N : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (pl:o.partition.length≤N) :
 (groupOutputAnswerMeter (groupRunOutputLocalSource actual T S A B C q o).value).work≤4*N+34 ∧
 (groupRunOutputLocalSource actual T S A B C q o).value.trace.length≤2 ∧
 (∀F,(groupOutputAnswerMeter (groupRunOutputLocalSource actual T S A B C q o).value).value=some F→
   F.length≤2*N ∧ F.flatten.length≤4*N):=by
 simp only [groupRunOutputLocalSource]
 split
 · cases hj:(groupJobsForMeter T S A B C o).value with
   | none=>simp only [groupOutputAnswerMeter,BothBadGrouped.OutputResult.trace,List.length_nil,Charged.work,Charged.value]
           exact ⟨by omega,by omega,by intro F h;cases h⟩
   | some js=>
     have j:BothBadGrouped.jobsFor T S A B C o=some js:=by simpa only [groupJobsForMeter_value] using hj
     have len:js.length=2:=(groupJobsFor_caps T S A B C o N tn sn pl js j).1
     let r:=literalScheduleSource (groupCallbackMeter actual) (q-o.sourceCuts.length) js
     have traces:r.value.queries.length≤2:=by
      rw [literalScheduleSource_queries]
      exact Nat.le_trans (scheduleSourceMeter_queries_bound _ _ js) (by omega)
     change (groupOutputAnswerMeter (.scheduled r.value)).work≤_ ∧ r.value.queries.length≤2 ∧ _
     refine ⟨?_,traces,?_⟩
     · cases ha:r.value.value.answers with
       | none=>simp only [groupOutputAnswerMeter,optionFlattenMeter,ha];omega
       | some xs=>
         have payload:=groupedJobsFor_schedule_payload actual T S A B C o js j N _ tn xs ha
         have bill:=answerFlattenMeter_bound xs N (by intro x hm;exact (payload.2 x hm).1)
         rw [payload.1] at bill
         simp only [groupOutputAnswerMeter,optionFlattenMeter,ha];omega
     · intro F hf
       change (optionFlattenMeter r.value.value.answers).value=some F at hf
       rw [optionFlattenMeter_value] at hf
       cases ha:r.value.value.answers with
       | none=>simp only [ha,Option.map_none] at hf;cases hf
       | some xs=>
         have eq:xs.flatMap Prod.snd=F:=by simpa only [ha,Option.map_some,Option.some.injEq] using hf
         subst F
         have payload:=groupedJobsFor_schedule_payload actual T S A B C o js j N _ tn xs ha
         have caps:=flatten_answer_caps xs N (by intro x hm;have p:=payload.2 x hm;exact ⟨p.1,by omega⟩)
         rw [payload.1] at caps
         exact ⟨by omega,by omega⟩
 · simp only [groupOutputAnswerMeter,BothBadGrouped.OutputResult.trace,List.length_nil,Charged.work,Charged.value]
   exact ⟨by omega,by omega,by intro F h;cases h⟩
end OrdinaryDispatch.Hard2SourceWork
