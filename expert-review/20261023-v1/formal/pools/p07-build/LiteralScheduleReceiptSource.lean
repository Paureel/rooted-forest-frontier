import BothBadPlanSource
namespace OrdinaryDispatch.Hard2SourceWork
open Universal233 WholeSourceWork PaidQueries
structure LiteralReceiptSource (P A : Type) where
 value : MeterReceipt P A
 localWork : Nat
 callbackWork : Nat

def literalRunSource {P A : Type} (f : P→Nat→Charged (Option (Nat×A))) (b : Nat) :
 List (Job P A)→LiteralReceiptSource P A
 | []=>⟨⟨⟨some [],[],0⟩,[],2,0⟩,2,0⟩
 | .resolved _ c a::js=>let r:=literalRunSource f b js
   ⟨⟨⟨r.value.value.answers.map ((c,a)::·),r.value.value.calls,r.value.value.visits+1⟩,
     r.value.queries,r.value.callerWork+5,r.value.recursiveWork⟩,r.localWork+32,r.callbackWork⟩
 | .hard p::js=>let a:=f p b
   match a.value with
   | none=>⟨⟨⟨none,[b],1⟩,[(p,b)],8,0⟩,32,a.work⟩
   | some x=>let r:=literalRunSource f b js
     ⟨⟨⟨r.value.value.answers.map (x::·),b::r.value.value.calls,r.value.value.visits+1⟩,
       (p,b)::r.value.queries,r.value.callerWork+8,r.value.recursiveWork⟩,
       r.localWork+32,a.work+r.callbackWork⟩
@[simp] theorem literalRunSource_value {P A : Type} (f : P→Nat→Charged (Option (Nat×A)))
 (b : Nat) (js : List (Job P A)) :
 (literalRunSource f b js).value=meterRun (fun p b=>(f p b).value) (fun _ _=>0) b js:=by
 induction js with
 | nil=>rfl
 | cons j js ih=>cases j with
   | resolved p c a=>simp only [literalRunSource,meterRun,ih]
   | hard p=>cases h:(f p b).value <;> simp only [literalRunSource,meterRun,h,ih,Nat.zero_add]

theorem literalRunSource_work {P A : Type} (f : P→Nat→Charged (Option (Nat×A)))
 (b : Nat) (js : List (Job P A)) :
 (literalRunSource f b js).localWork=(runSourceMeter f b js).callerWork ∧
 (literalRunSource f b js).callbackWork=(runSourceMeter f b js).recursiveWork:=by
 induction js with
 | nil=>exact ⟨rfl,rfl⟩
 | cons j js ih=>cases j with
   | resolved p c a=>simpa only [literalRunSource,runSourceMeter] using ⟨congrArg (·+32) ih.1,ih.2⟩
   | hard p=>cases h:(f p b).value <;> simp [literalRunSource,runSourceMeter,h,ih]

/-- Original receipt fields, including declared callerWork, are constructed
literally. Their computation is paid in localWork; the declared value is not
adopted as the source bill. -/
def literalScheduleSource {P A : Type} (f : P→Nat→Charged (Option (Nat×A)))
 (q : Nat) (js : List (Job P A)) : LiteralReceiptSource P A:=
 let k:=knownCostMeter js;let p:=pendingMeter js
 if q<k.value+2*p.value then
  ⟨⟨⟨none,[],0⟩,[],8*js.length+8,0⟩,k.work+p.work+js.length+24,0⟩ else
 let b:=allocatedMeter q js;let r:=literalRunSource f b.value js
 let a:=acceptAnswersMeter q r.value.value.answers
 let pc:=postChargeMeter r.value.value
 ⟨⟨⟨a.value,r.value.value.calls,r.value.value.visits⟩,r.value.queries,
     16*js.length+20+r.value.callerWork+pc.value,r.value.recursiveWork⟩,
   k.work+p.work+b.work+r.localWork+a.work+pc.work+js.length+40,r.callbackWork⟩
@[simp] theorem literalScheduleSource_value {P A : Type} (f : P→Nat→Charged (Option (Nat×A)))
 (q : Nat) (js : List (Job P A)) :
 (literalScheduleSource f q js).value=meterSchedule (fun p b=>(f p b).value) (fun _ _=>0) q js:=by
 simp only [literalScheduleSource,meterSchedule,knownCostMeter_value,pendingMeter_value,
  allocatedMeter_value,literalRunSource_value,acceptAnswersMeter_value,postChargeMeter_value]
 split <;> rfl

theorem literalScheduleSource_work {P A : Type} (f : P→Nat→Charged (Option (Nat×A)))
 (q : Nat) (js : List (Job P A)) :
 (literalScheduleSource f q js).localWork=(scheduleSourceMeter f q js).callerWork ∧
 (literalScheduleSource f q js).callbackWork=(scheduleSourceMeter f q js).recursiveWork:=by
 have rv:(literalRunSource f (allocated q js) js).value.value=(runSourceMeter f (allocated q js) js).value:=by
  rw [literalRunSource_value,meterRun_value,runSourceMeter_value]
 have work:=literalRunSource_work f (allocated q js) js
 simp only [literalScheduleSource,scheduleSourceMeter,knownCostMeter_value,pendingMeter_value,allocatedMeter_value]
 split
 · exact ⟨rfl,rfl⟩
 · simp [rv,work.1,work.2,meterRun_value]
end OrdinaryDispatch.Hard2SourceWork
