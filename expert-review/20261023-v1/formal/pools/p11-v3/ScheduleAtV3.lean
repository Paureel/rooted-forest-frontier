import SelectedChildrenV2

namespace SourceForestV3
open Universal233.PaidQueries SourceCouplingV2
open CallbackPairingAuthor (indexFrom indexFrom_length)

variable {P A : Type}

-- The exact scheduler at the caller's next ordinal. Operational constructors
-- still take concrete child executions; no source solver or fee is a runtime input.
inductive ScheduleAt (Child : P → Nat → Option (Nat × A) → Prop) (mode : Mode)
    (q : Nat) (js : List (Job P A)) (k : Nat) :
    MeterReceipt P A → List (Slot P A) → Prop
  | refused (small : q < knownCost js+2*pending js) :
      ScheduleAt Child mode q js k ⟨⟨none,[],0⟩,[],8*js.length+8,0⟩ []
  | run {r : MeterReceipt P A} {slots : List (Slot P A)} {ticks : Nat}
      (enough : ¬q < knownCost js+2*pending js)
      (execution : Run Child mode (allocated q js) k js r slots ticks) :
      ScheduleAt Child mode q js k (scheduledReceipt q js r) slots

variable {Child : P → Nat → Option (Nat × A) → Prop} {mode : Mode}
  {q k : Nat} {js : List (Job P A)} {r : MeterReceipt P A} {slots : List (Slot P A)}
  {spec : P → Nat → Option (Nat × A)}

theorem scheduleAt_projection (h : ScheduleAt Child mode q js k r slots)
    (sound : ∀ p b a, Child p b a → a=spec p b) :
    r=meterSchedule (specCallback mode spec) (fun _ _=>0) q js := by
  cases h with
  | refused small => simp [meterSchedule,small]
  | run enough execution =>
    have hr := run_projection execution sound
    simpa only [meterSchedule,enough,↓reduceIte,scheduledReceipt] using
      congrArg (scheduledReceipt q js) hr

theorem scheduleAt_index (h : ScheduleAt Child mode q js k r slots) :
    slots.map (fun s=>(s.index,s.query))=indexFrom k r.queries := by
  cases h with
  | refused small => rfl
  | run enough execution =>
    have hi := run_slot_index execution
    exact hi

theorem scheduleAt_exists (total : ∀ p b, ∃ a, Child p b a)
    (mode : Mode) (q k : Nat) (js : List (Job P A)) :
    ∃ r slots, ScheduleAt Child mode q js k r slots := by
  by_cases hs : q < knownCost js+2*pending js
  · exact ⟨_,_,ScheduleAt.refused hs⟩
  · obtain ⟨r,slots,ticks,hr⟩ := run_exists total mode (allocated q js) k js
    exact ⟨_,_,ScheduleAt.run hs hr⟩

theorem indexFrom_append {α : Type} (k : Nat) (xs ys : List α) :
    indexFrom k (xs++ys)=indexFrom k xs++indexFrom (k+xs.length) ys := by
  induction xs generalizing k with
  | nil => simp [indexFrom]
  | cons x xs ih => simp [indexFrom,ih,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem index_length {qs : List (P × Nat)}
    (h : slots.map (fun s=>(s.index,s.query))=indexFrom k qs) : slots.length=qs.length := by
  have hl := congrArg List.length h
  simpa only [List.length_map,indexFrom_length] using hl

end SourceForestV3
