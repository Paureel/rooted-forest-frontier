import GroupedRunOutputBound
import GroupedExecutionSource
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState ForestGroups Universal233 WholeSourceWork CoreWork
open GenericForest GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open Universal233.GroupedFullQuery Universal233.PaidQueries Universal233.Rule5SelectedLocalWork

/-- Every prepared job preserves its original full group problem. Resolved
answers satisfy the original full current-forest checker. -/
theorem groupedPrepared_payload (ps : List Problem) (js : List (Job Problem (List (List Nat))))
 (prep:prepare ps=some js) (N : Nat)
 (caps:∀p,p∈ps→targetNodes p.target≤N)
 (p : Problem) (c : Nat) (F : List (List Nat)) (mem:Job.resolved p c F∈js) :
 F.length≤N ∧ F.flatten.length≤N:=by
 have spec:=prepare_spec ps js prep
 have planned:=spec.2 (.resolved p c F) mem
 have pmem:p∈ps:=by rw [←spec.1];exact List.mem_map.2 ⟨.resolved p c F,mem,rfl⟩
 have payload:=state_payload_of_agrees p.target p.sources F planned.1
 have cap:=Nat.le_trans (labels_nodes p.target) (caps p pmem)
 exact ⟨Nat.le_trans payload.1 cap,Nat.le_trans payload.2 cap⟩

theorem groupCallbackMeter_payload (actual : GenericForest.FrontierWork.Ordinary) (p : Problem)
 (b N : Nat) (tn:targetNodes p.target≤N) (x : Nat×List (List Nat))
 (h:(groupCallbackMeter actual p b).value=some x) : x.2.length≤N ∧ x.2.flatten.length≤N:=by
 simp only [groupCallbackMeter] at h
 cases ans:GenericForest.solve actual p.target p.sources b with
 | none=>simp only [ans] at h;cases h
 | some F=>
   have eq:x=((additionalCostMeter p.sources F).value,F):=by simpa only [ans,Option.some.injEq] using h.symm
   subst x
   have payload:=state_payload_forest_return actual p.target p.sources b F ans
   have cap:=Nat.le_trans (labels_nodes p.target) tn
   exact ⟨Nat.le_trans payload.1 cap,Nat.le_trans payload.2 cap⟩

theorem groupedSchedule_payload (actual : GenericForest.FrontierWork.Ordinary) (ps : List Problem)
 (js : List (Job Problem (List (List Nat)))) (prep:prepare ps=some js) (N b : Nat)
 (caps:∀p,p∈ps→targetNodes p.target≤N) (xs : List (Nat×List (List Nat)))
 (h:(literalScheduleSource (groupCallbackMeter actual) b js).value.value.answers=some xs) :
 xs.length=ps.length ∧ ∀x,x∈xs→x.2.length≤N ∧ x.2.flatten.length≤N:=by
 have hh:(scheduleSourceMeter (groupCallbackMeter actual) b js).value.answers=some xs:=by
  simpa only [literalScheduleSource_value,meterSchedule_value,scheduleSourceMeter_value] using h
 have spec:=prepare_spec ps js prep
 have cap:=scheduleSourceMeter_answer_payload (groupCallbackMeter actual) b js
  (fun F=>F.length≤N ∧ F.flatten.length≤N)
  (groupedPrepared_payload ps js prep N caps)
  (by
   intro p hm x ha
   have pmem:p∈ps:=by rw [←spec.1];exact List.mem_map.2 ⟨.hard p,hm,rfl⟩
   exact groupCallbackMeter_payload actual p _ N (caps p pmem) x ha) xs hh
 have len:=congrArg List.length spec.1
 simp only [List.length_map] at len
 exact ⟨cap.1.trans len,cap.2⟩
end OrdinaryDispatch.Hard2SourceWork
