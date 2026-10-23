import QueryWork
import IndexOrder

namespace SourceCouplingV2
open Universal233.PaidQueries
open CallbackPairingAuthor (indexFrom indexFrom_project)

variable {P A : Type}

inductive Mode where
  | direct
  | cutoff (parent : Nat)

def enabled : Mode → Nat → Bool
  | .direct, _ => true
  | .cutoff q, b => decide (b < q)

-- Specification only: never an input to the operational constructors below.
def specCallback (mode : Mode) (spec : P → Nat → Option (Nat × A))
    (p : P) (b : Nat) : Option (Nat × A) :=
  if enabled mode b then spec p b else none

structure Slot (P A : Type) where
  index : Nat
  query : P × Nat
  returned : Option (Nat × A)
  live : Bool

def emptyReceipt : MeterReceipt P A := ⟨⟨some [],[],0⟩,[],2,0⟩
def resolvedReceipt (c : Nat) (a : A) (r : MeterReceipt P A) : MeterReceipt P A :=
  ⟨⟨r.value.answers.map ((c,a)::·),r.value.calls,r.value.visits+1⟩,
    r.queries,r.callerWork+5,r.recursiveWork⟩
def failedReceipt (p : P) (b : Nat) : MeterReceipt P A :=
  ⟨⟨none,[b],1⟩,[(p,b)],8,0⟩
def successReceipt (p : P) (b : Nat) (x : Nat × A) (r : MeterReceipt P A) : MeterReceipt P A :=
  ⟨⟨r.value.answers.map (x::·),b::r.value.calls,r.value.visits+1⟩,
    (p,b)::r.queries,r.callerWork+8,0+r.recursiveWork⟩

-- Scheduler-specific request/return execution. Child is an execution relation,
-- not a runtime answer function, fee oracle, table, or cache. A live constructor
-- requires the actual child's return; cutoff refusal allocates its slot locally.
inductive Run (Child : P → Nat → Option (Nat × A) → Prop) (mode : Mode)
    (b : Nat) : Nat → List (Job P A) → MeterReceipt P A → List (Slot P A) → Nat → Prop
  | nil : Run Child mode b k [] emptyReceipt [] 16
  | resolved (tail : Run Child mode b k js r slots ticks) :
      Run Child mode b k (.resolved p c a::js) (resolvedReceipt c a r) slots (ticks+24)
  | refused (off : enabled mode b = false) :
      Run Child mode b k (.hard p::js) (failedReceipt p b)
        [⟨k,(p,b),none,false⟩] 32
  | failed (on : enabled mode b = true) (returned : Child p b none) :
      Run Child mode b k (.hard p::js) (failedReceipt p b)
        [⟨k,(p,b),none,true⟩] 32
  | success (on : enabled mode b = true) (returned : Child p b (some x))
      (tail : Run Child mode b (k+1) js r slots ticks) :
      Run Child mode b k (.hard p::js) (successReceipt p b x r)
        (⟨k,(p,b),some x,true⟩::slots) (ticks+32)

variable {Child : P → Nat → Option (Nat × A) → Prop}
  {mode : Mode} {spec : P → Nat → Option (Nat × A)}
  {b k q ticks : Nat} {js : List (Job P A)}
  {r : MeterReceipt P A} {slots : List (Slot P A)}

theorem run_projection
    (h : Run Child mode b k js r slots ticks)
    (sound : ∀ p b a, Child p b a → a = spec p b) :
    r = meterRun (specCallback mode spec) (fun _ _=>0) b js := by
  induction h with
  | nil => rfl
  | resolved tail ih =>
    simpa only [meterRun, resolvedReceipt] using congrArg (resolvedReceipt _ _) ih
  | refused off => simp [meterRun, specCallback, off, failedReceipt]
  | failed on returned =>
    have answer := (sound _ _ _ returned).symm
    simp [meterRun, specCallback, on, answer, failedReceipt]
  | success on returned tail ih =>
    have answer := (sound _ _ _ returned).symm
    simpa only [meterRun, specCallback, on, Bool.true_eq, ↓reduceIte, answer,
      successReceipt] using congrArg (successReceipt _ _ _) ih

theorem run_slot_index (h : Run Child mode b k js r slots ticks) :
    slots.map (fun s => (s.index,s.query)) = indexFrom k r.queries := by
  induction h with
  | nil => rfl
  | resolved tail ih => exact ih
  | refused off => rfl
  | failed on returned => rfl
  | success on returned tail ih =>
    simpa only [List.map_cons, successReceipt, indexFrom] using congrArg (List.cons _) ih

theorem run_slot_queries (h : Run Child mode b k js r slots ticks) :
    slots.map Slot.query = r.queries := by
  have z := congrArg (List.map Prod.snd) (run_slot_index h)
  simpa only [List.map_map, indexFrom_project, Function.comp_def] using z

theorem run_tick_credit (h : Run Child mode b k js r slots ticks) :
    ticks ≤ 8*r.callerWork := by
  induction h with
  | nil => simp [emptyReceipt]
  | resolved tail ih => simp only [resolvedReceipt]; omega
  | refused off => simp [failedReceipt]
  | failed on returned => simp [failedReceipt]
  | success on returned tail ih => simp only [successReceipt]; omega

def liveSlots (slots : List (Slot P A)) : List (Slot P A) := slots.filter Slot.live

theorem live_order (slots : List (Slot P A)) : (liveSlots slots).Sublist slots := by
  exact List.filter_sublist

theorem run_recursiveWork_zero (h : Run Child mode b k js r slots ticks) :
    r.recursiveWork = 0 := by
  induction h with
  | nil => rfl
  | resolved tail ih => exact ih
  | refused off => rfl
  | failed on returned => rfl
  | success on returned tail ih => simpa [successReceipt] using ih

def scheduledReceipt (q : Nat) (js : List (Job P A)) (r : MeterReceipt P A) : MeterReceipt P A :=
  ⟨⟨r.value.answers.bind (fun xs => if answerCost xs ≤ q then some xs else none),
    r.value.calls,r.value.visits⟩,r.queries,
    16*js.length+20+r.callerWork+postCharge r.value,r.recursiveWork⟩

inductive Schedule (Child : P → Nat → Option (Nat × A) → Prop) (mode : Mode)
    (q : Nat) (js : List (Job P A)) : MeterReceipt P A → List (Slot P A) → Nat → Prop
  | refused (small : q < knownCost js+2*pending js) :
      Schedule Child mode q js ⟨⟨none,[],0⟩,[],8*js.length+8,0⟩ [] (64*js.length+64)
  | run {rr : MeterReceipt P A} {ss : List (Slot P A)} {tt : Nat}
      (enough : ¬ q < knownCost js+2*pending js)
      (execution : Run Child mode (allocated q js) 0 js rr ss tt) :
      Schedule Child mode q js (scheduledReceipt q js rr) ss
        (tt+64*js.length+64+8*postCharge rr.value)

theorem schedule_projection (h : Schedule Child mode q js r slots ticks)
    (sound : ∀ p b a, Child p b a → a = spec p b) :
    r = meterSchedule (specCallback mode spec) (fun _ _=>0) q js := by
  cases h with
  | refused small => simp [meterSchedule, small]
  | run enough execution =>
    have hr := run_projection execution sound
    simpa only [meterSchedule, enough, ↓reduceIte, scheduledReceipt] using
      congrArg (scheduledReceipt q js) hr

theorem schedule_slot_index (h : Schedule Child mode q js r slots ticks) :
    slots.map (fun s => (s.index,s.query)) = indexFrom 0 r.queries := by
  cases h with
  | refused small => rfl
  | run enough execution =>
    have hs := run_slot_index execution
    exact hs

theorem schedule_tick_credit (h : Schedule Child mode q js r slots ticks) :
    ticks ≤ 8*r.callerWork := by
  cases h with
  | refused small => simp; omega
  | run enough execution =>
    have ih := run_tick_credit execution
    simp only [scheduledReceipt]
    omega

end SourceCouplingV2
