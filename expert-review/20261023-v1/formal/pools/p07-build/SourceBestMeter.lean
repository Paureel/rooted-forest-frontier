import BothBadPlannerAtoms
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF Universal233 WholeSourceWork CoreWork

/-- Literal best with measured predicates and both literal score computations.
The complete recursive tail is billed even when the head is invalid. -/
def sourceBestMeter {α : Type} (cost : α→Charged Nat) (valid : α→Charged Bool) : List α→Charged (Option α)
 | []=>⟨none,2⟩
 | x::xs=>let a:=valid x;let r:=sourceBestMeter cost valid xs
   if a.value then
    match r.value with
    | none=>⟨some x,a.work+r.work+8⟩
    | some y=>let cx:=cost x;let cy:=cost y
              ⟨if cx.value≤cy.value then some x else some y,a.work+r.work+cx.work+cy.work+12⟩
   else ⟨r.value,a.work+r.work+8⟩
@[simp] theorem sourceBestMeter_value {α : Type} (cost : α→Charged Nat) (valid : α→Charged Bool) (xs : List α) :
 (sourceBestMeter cost valid xs).value=best (fun x=>(cost x).value) (fun x=>(valid x).value) xs:=by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>
   by_cases h:(valid x).value=true
   · simp only [sourceBestMeter,best,h,ite_true]
     rw [←ih]
     cases ht:(sourceBestMeter cost valid xs).value <;> rfl
   · simp [sourceBestMeter,best,h,ih]
end OrdinaryDispatch.Hard2SourceWork
