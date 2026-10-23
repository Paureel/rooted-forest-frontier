import OrdinaryPrepareBound
namespace OrdinaryDispatch.Hard2SourceWork
open Universal233 WholeSourceWork PaidQueries

def knownCostMeter {P A : Type} : List (Job P A)→Charged Nat
 | []=>⟨0,2⟩
 | .resolved _ c _::js=>let r:=knownCostMeter js;⟨c+r.value,r.work+8⟩
 | .hard _::js=>let r:=knownCostMeter js;⟨r.value,r.work+8⟩
@[simp] theorem knownCostMeter_value {P A : Type} (js : List (Job P A)) :
 (knownCostMeter js).value=knownCost js:=by induction js with
 | nil=>rfl
 | cons j js ih=>cases j <;> simp [knownCostMeter,knownCost,ih]
theorem knownCostMeter_work {P A : Type} (js : List (Job P A)) :
 (knownCostMeter js).work=8*js.length+2:=by induction js with
 | nil=>rfl
 | cons j js ih=>cases j <;> simp [knownCostMeter,ih,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def pendingMeter {P A : Type} : List (Job P A)→Charged Nat
 | []=>⟨0,2⟩
 | .resolved _ _ _::js=>let r:=pendingMeter js;⟨r.value,r.work+8⟩
 | .hard _::js=>let r:=pendingMeter js;⟨1+r.value,r.work+8⟩
@[simp] theorem pendingMeter_value {P A : Type} (js : List (Job P A)) :
 (pendingMeter js).value=pending js:=by induction js with
 | nil=>rfl
 | cons j js ih=>cases j <;> simp [pendingMeter,pending,ih]
theorem pendingMeter_work {P A : Type} (js : List (Job P A)) :
 (pendingMeter js).work=8*js.length+2:=by induction js with
 | nil=>rfl
 | cons j js ih=>cases j <;> simp [pendingMeter,ih,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def answerCostMeter {A : Type} : List (Nat×A)→Charged Nat
 | []=>⟨0,2⟩
 | x::xs=>let r:=answerCostMeter xs;⟨x.1+r.value,r.work+8⟩
@[simp] theorem answerCostMeter_value {A : Type} (xs : List (Nat×A)) :
 (answerCostMeter xs).value=answerCost xs:=by induction xs <;> simp_all [answerCostMeter,answerCost]
theorem answerCostMeter_work {A : Type} (xs : List (Nat×A)) :
 (answerCostMeter xs).work=8*xs.length+2:=by induction xs <;> simp_all [answerCostMeter,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def allocatedMeter {P A : Type} (q : Nat) (js : List (Job P A)) : Charged Nat:=
 let k:=knownCostMeter js;let p:=pendingMeter js
 ⟨q-k.value-2*(p.value-1),k.work+p.work+8⟩
@[simp] theorem allocatedMeter_value {P A : Type} (q : Nat) (js : List (Job P A)) :
 (allocatedMeter q js).value=allocated q js:=by simp [allocatedMeter,allocated]
theorem allocatedMeter_work {P A : Type} (q : Nat) (js : List (Job P A)) :
 (allocatedMeter q js).work=16*js.length+12:=by simp [allocatedMeter,knownCostMeter_work,pendingMeter_work];omega

/-- Meter the original postCharge computation, including List.length. Its
returned declared fee is a value; it is not adopted as this source bill. -/
def postChargeMeter {A : Type} (r : Receipt A) : Charged Nat:=
 match r.answers with | none=>⟨4,4⟩ | some xs=>⟨4*xs.length+4,xs.length+8⟩
@[simp] theorem postChargeMeter_value {A : Type} (r : Receipt A) :
 (postChargeMeter r).value=postCharge r:=by cases h:r.answers <;> simp [postChargeMeter,postCharge,h]
end OrdinaryDispatch.Hard2SourceWork
