import CompleteWeightedSource
import CoupledChildrenV2

namespace SourceLocalCreditV2
open RMAF OrdinaryDispatch

theorem front_positive (q : Nat) (T S : Tree) :
    1 ≤ (EarlyLocalWork.meterFront q T S).work := by
  unfold EarlyLocalWork.meterFront
  dsimp only
  split
  · split <;> dsimp only <;> omega
  · dsimp only
    omega

theorem localDebit_positive (q : Nat) (T S : Tree) :
    1 ≤ CompleteSource.completeLocalDebit T S q := by
  have hp := front_positive q T S
  unfold CompleteSource.completeLocalDebit CompleteSource.ordinaryCompleteStepSource
  dsimp only
  split <;> dsimp only <;> omega

end SourceLocalCreditV2

namespace SourceCouplingV2
open Universal233.PaidQueries

variable {P A : Type}

theorem meterRun_value (spec : P → Nat → Option (Nat × A)) (b : Nat) (js : List (Job P A)) :
    (meterRun spec (fun _ _=>0) b js).value = run spec b js := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    cases j with
    | resolved p c a =>
      simpa [meterRun,run] using (congrArg
        (fun r : Receipt A => (⟨r.answers.map ((c,a)::·),r.calls,r.visits+1⟩ : Receipt A)) ih)
    | hard p =>
      cases h : spec p b with
      | none => simp [meterRun,run,h]
      | some x =>
        simpa [meterRun,run,h] using (congrArg
          (fun r : Receipt A => (⟨r.answers.map (x::·),b::r.calls,r.visits+1⟩ : Receipt A)) ih)

theorem meterSchedule_value (spec : P → Nat → Option (Nat × A)) (q : Nat) (js : List (Job P A)) :
    (meterSchedule spec (fun _ _=>0) q js).value = schedule spec q js := by
  unfold meterSchedule schedule
  split
  · rfl
  · have h := meterRun_value spec (allocated q js) js
    rw [←h]

theorem coupled_schedule_value {P A : Type} {Child : P → Nat → Option (Nat × A) → Prop}
    {spec : P → Nat → Option (Nat × A)}
    {mode : Mode} {q ticks : Nat} {js : List (Job P A)}
    {r : MeterReceipt P A} {slots : List (Slot P A)}
    (h : Schedule Child mode q js r slots ticks)
    (sound : ∀ p b a, Child p b a → a=spec p b) :
    r.value = schedule (specCallback mode spec) q js := by
  rw [schedule_projection h sound]
  exact meterSchedule_value _ _ _

end SourceCouplingV2
