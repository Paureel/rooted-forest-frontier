import DisjointRunExecutionV3

namespace SourceMafCallbackV3
open RMAF SourceForestV3
variable {T S : Tree}
theorem maf_slots_realize (h : MafExec OrdExec mode T S U b k ret) :
    ∀ s∈ret.slots,SlotRealizes OrdExec mode s := by
  cases h with
  | missing absent => simp [missingReturn]
  | returned left right execution => exact forest_slots_realize _ _ _ _ _ execution
end SourceMafCallbackV3

namespace SourceRetainedSchedulerV3
open RMAF SourceForestV3 SourceMafCallbackV3
variable {T S : Tree}
theorem run_slots_realize (h : Run OrdExec mode T S b k js r calls debits slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  induction h with
  | nil => simp
  | resolved tail ih => exact ih
  | failed head empty => exact maf_slots_realize head
  | succeeded head answer tail ih =>
    intro s hs
    rcases List.mem_append.mp hs with hs|hs
    · exact maf_slots_realize head s hs
    · exact ih s hs

theorem schedule_slots_realize (h : Schedule OrdExec mode T S q js k r calls debits slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | refused small => simp
  | run enough execution => exact run_slots_realize execution
end SourceRetainedSchedulerV3

namespace SourceOrdinaryLocalV3
open RMAF SourceForestV3
variable {T S : Tree} {Q : List (List Nat)}
theorem local_slots_realize (h : LocalExec OrdExec mode T S Q b k r debits slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | refused none => simp
  | prepared some execution => exact SourceRetainedSchedulerV3.schedule_slots_realize execution
end SourceOrdinaryLocalV3

namespace SourceDisjointQueryV3
open RMAF SourceForestV3
variable {T S : Tree}
theorem query_slots_realize (h : QueryExec OrdExec mode T S parts q k r slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | refused over => simp
  | returned paid execution => exact SourceOrdinaryLocalV3.local_slots_realize execution
end SourceDisjointQueryV3

namespace SourceDisjointRunV3
open RMAF SourceForestV3
variable {T S : Tree}
theorem disjoint_slots_realize (h : DisjointExec OrdExec mode T S a b q out calls slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | run children query =>
    intro s hs
    rcases List.mem_append.mp hs with hs|hs
    · exact children_slots_realize children s hs
    · exact SourceDisjointQueryV3.query_slots_realize query s hs
end SourceDisjointRunV3
