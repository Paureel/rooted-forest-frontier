import ForestSingletonV2

namespace SourceCoupledControlsV2
open Universal233.PaidQueries SourceCouplingV2

-- A constructed deterministic child programme, used only as planted truth.
def toySpec (p b : Nat) : Option (Nat × Nat) := if p=4 then some (0,7) else none
inductive ToyChild : Nat → Nat → Option (Nat × Nat) → Prop
  | four (b : Nat) : ToyChild 4 b (some (0,7))
  | five (b : Nat) : ToyChild 5 b none

theorem toy_sound (h : ToyChild p b a) : a=toySpec p b := by
  cases h <;> simp [toySpec]

def duplicateReceipt : MeterReceipt Nat Nat :=
  successReceipt 4 2 (0,7) (successReceipt 4 2 (0,7) emptyReceipt)
def duplicateSlots : List (Slot Nat Nat) :=
  [⟨0,(4,2),some (0,7),true⟩,⟨1,(4,2),some (0,7),true⟩]

theorem duplicate_execution : Run ToyChild .direct 2 0
    [.hard 4,.hard 4] duplicateReceipt duplicateSlots 80 := by
  exact Run.success rfl (ToyChild.four 2) (Run.success rfl (ToyChild.four 2) Run.nil)

theorem duplicate_source_fields : duplicateReceipt =
    meterRun (specCallback .direct toySpec) (fun _ _=>0) 2 [.hard 4,.hard 4] :=
  run_projection duplicate_execution (fun _ _ _ h=>toy_sound h)

theorem refusal_execution : Run ToyChild (.cutoff 2) 2 0
    [.hard 4] (failedReceipt 4 2) [⟨0,(4,2),none,false⟩] 32 := by
  exact Run.refused rfl

#guard duplicateReceipt.value.answers == some [(0,7),(0,7)]
#guard duplicateReceipt.value.calls == [2,2]
#guard duplicateReceipt.value.visits == 2
#guard duplicateReceipt.queries == [(4,2),(4,2)]
#guard duplicateReceipt.callerWork == 18
#guard duplicateReceipt.recursiveWork == 0
#guard (liveSlots ([⟨0,(4,2),none,false⟩] : List (Slot Nat Nat))).length == 0
#guard (failedReceipt (A:=Nat) 4 2).queries == [(4,2)]

end SourceCoupledControlsV2
