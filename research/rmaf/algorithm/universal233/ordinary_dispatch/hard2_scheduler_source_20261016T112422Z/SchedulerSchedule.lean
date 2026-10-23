import SchedulerRun
namespace OrdinaryDispatch.Hard2SourceWork
open Universal233 WholeSourceWork PaidQueries

def acceptAnswersMeter {A : Type} (q : Nat) : Option (List (Nat×A))→Charged (Option (List (Nat×A)))
 | none=>⟨none,4⟩
 | some xs=>let a:=answerCostMeter xs
   ⟨if a.value≤q then some xs else none,a.work+8⟩
@[simp] theorem acceptAnswersMeter_value {A : Type} (q : Nat) (xs : Option (List (Nat×A))) :
 (acceptAnswersMeter q xs).value=xs.bind (fun ys=>if answerCost ys≤q then some ys else none):=by
 cases xs <;> simp [acceptAnswersMeter]

/-- The preprocessing and allocation expressions each perform their own scans.
The declared postCharge is computed and charged only for computing its value.
All callback work is still stored separately at its actual query. -/
def scheduleSourceMeter {P A : Type} (f : P→Nat→Charged (Option (Nat×A)))
 (q : Nat) (js : List (Job P A)) : MeterReceipt P A:=
 let k:=knownCostMeter js;let p:=pendingMeter js
 if q<k.value+2*p.value then ⟨⟨none,[],0⟩,[],k.work+p.work+js.length+24,0⟩ else
 let b:=allocatedMeter q js
 let r:=runSourceMeter f b.value js
 let a:=acceptAnswersMeter q r.value.answers
 let pc:=postChargeMeter r.value
 ⟨⟨a.value,r.value.calls,r.value.visits⟩,r.queries,
   k.work+p.work+b.work+r.callerWork+a.work+pc.work+js.length+40,r.recursiveWork⟩

@[simp] theorem scheduleSourceMeter_value {P A : Type}
 (f : P→Nat→Charged (Option (Nat×A))) (q : Nat) (js : List (Job P A)) :
 (scheduleSourceMeter f q js).value=schedule (fun p b=>(f p b).value) q js:=by
 simp only [scheduleSourceMeter,schedule,knownCostMeter_value,pendingMeter_value,
  allocatedMeter_value,acceptAnswersMeter_value,runSourceMeter_value]
 split <;> rfl

theorem scheduleSourceMeter_queries {P A : Type}
 (f : P→Nat→Charged (Option (Nat×A))) (q : Nat) (js : List (Job P A)) :
 (scheduleSourceMeter f q js).queries=
  (meterSchedule (fun p b=>(f p b).value) (fun _ _=>0) q js).queries:=by
 simp only [scheduleSourceMeter,meterSchedule,knownCostMeter_value,pendingMeter_value,allocatedMeter_value]
 split
 · rfl
 · exact runSourceMeter_queries f _ js

theorem scheduleSourceMeter_callback_split {P A : Type}
 (f : P→Nat→Charged (Option (Nat×A))) (q : Nat) (js : List (Job P A)) :
 (scheduleSourceMeter f q js).recursiveWork=
  ((scheduleSourceMeter f q js).queries.map (fun pb=>(f pb.1 pb.2).work)).sum:=by
 simp only [scheduleSourceMeter,knownCostMeter_value,pendingMeter_value]
 split
 · rfl
 · exact runSourceMeter_callback_split f _ js

theorem scheduleSourceMeter_caller_bound {P A : Type}
 (f : P→Nat→Charged (Option (Nat×A))) (q : Nat) (js : List (Job P A)) :
 (scheduleSourceMeter f q js).callerWork≤128*(js.length+1):=by
 have k:=knownCostMeter_work js;have p:=pendingMeter_work js
 have b:=allocatedMeter_work q js
 have r:=runSourceMeter_caller_bound f (allocated q js) js
 have payload (xs : List (Nat×A))
  (h:(runSourceMeter f (allocated q js) js).value.answers=some xs) : xs.length=js.length:=by
  apply run_answer_length (fun p b=>(f p b).value) (allocated q js) js xs
  simpa only [runSourceMeter_value] using h
 have a:(acceptAnswersMeter q (runSourceMeter f (allocated q js) js).value.answers).work≤8*js.length+10:=by
  cases h:(runSourceMeter f (allocated q js) js).value.answers with
  | none=>simp [acceptAnswersMeter,h]
  | some xs=>simp [acceptAnswersMeter,h,answerCostMeter_work,payload xs h]
 have pc:(postChargeMeter (runSourceMeter f (allocated q js) js).value).work≤js.length+8:=by
  cases h:(runSourceMeter f (allocated q js) js).value.answers with
  | none=>simp only [postChargeMeter,h];omega
  | some xs=>simp only [postChargeMeter,h,payload xs h];omega
 simp only [scheduleSourceMeter,knownCostMeter_value,pendingMeter_value,allocatedMeter_value]
 split <;> dsimp only <;> omega

theorem scheduleSourceMeter_queries_bound {P A : Type}
 (f : P→Nat→Charged (Option (Nat×A))) (q : Nat) (js : List (Job P A)) :
 (scheduleSourceMeter f q js).queries.length≤js.length:=by
 simp only [scheduleSourceMeter,knownCostMeter_value,pendingMeter_value]
 split
 · simp
 · exact runSourceMeter_queries_bound f _ js

theorem scheduleSourceMeter_query_origin {P A : Type}
 (f : P→Nat→Charged (Option (Nat×A))) (q : Nat) (js : List (Job P A))
 (pb : P×Nat) (h:pb∈(scheduleSourceMeter f q js).queries) :
 .hard pb.1∈js ∧ pb.2=allocated q js:=by
 simp only [scheduleSourceMeter,knownCostMeter_value,pendingMeter_value,allocatedMeter_value] at h
 split at h
 · simp at h
 · exact runSourceMeter_query_origin f _ js pb h
end OrdinaryDispatch.Hard2SourceWork
