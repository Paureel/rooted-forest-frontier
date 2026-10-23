import Rule5CommonCorrespondenceV3

namespace SourceRule5CommonV3
open RMAF Universal233 SourceForestV3 Universal233.Rule5ExecutionSource
open SourceCouplingV2 (Mode)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode} {T S : Tree}

theorem paid_slot_budget (h : PaidExec OrdExec mode d q k FY FN r slots) :
    ∀ s∈slots,s.query.2<q := by
  cases h with
  | run jobs =>
    have hp:=congrArg (List.map Prod.snd) (SourceRule5CommonJobsV3.jobs_index jobs)
    simp only [List.map_map,Function.comp_def,CallbackPairingAuthor.indexFrom_project] at hp
    intro s hs
    have hm:s.query∈slots.map SourceCouplingV2.Slot.query:=List.mem_map.mpr ⟨s,hs,rfl⟩
    rw [hp] at hm
    by_cases zero:q=0
    · simp only [paidJobsMeter,zero,↓reduceIte,List.map_nil,List.mem_nil_iff] at hm
    · simp only [paidJobsMeter,zero,↓reduceIte,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with hm|hm
      all_goals have hb:=congrArg Prod.snd hm;dsimp at hb;omega

theorem outside_slot_budget (h : OutsideExec OrdExec mode d q k FY r slots) :
    ∀ s∈slots,s.query.2<q := by
  cases h with
  | refused empty => simp
  | paid found execution => exact paid_slot_budget execution

theorem guarded_slot_budget (h : GuardedExec OrdExec mode d q k r slots) :
    ∀ s∈slots,s.query.2<q := by
  cases h with
  | refused empty => simp
  | found selected execution => exact outside_slot_budget execution

theorem common_slot_budget (h : CommonExec OrdExec mode T S a b q k d r slots) :
    ∀ s∈slots,s.query.2<q := by
  cases h with
  | refused empty => simp
  | built found execution => exact guarded_slot_budget execution
end SourceRule5CommonV3
