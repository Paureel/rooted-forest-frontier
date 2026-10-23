import PaidUnitsCompleteV3

namespace SourcePaidUnitsV3
open RMAF Universal233 SourceForestV3
open SourceCouplingV2 (Mode)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem paid_units_distinct
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PaidUnitsExec OrdExec mode T S c q out r rec chrono) :
    rec.Pairwise (fun a b=>a.1≠b.1) := by
  cases h with
  | @run p pr pc u us paid units =>
    rw [recorded,List.pairwise_append]
    refine ⟨?_,?_,?_⟩
    · simp only [labelUnits,List.pairwise_map]
      exact (CallbackPairingAuthor.indexFrom_distinct 0 us).imp
        (fun h he=>h (congrArg (fun x=>x.2.2) he))
    · simp only [labelPaid,List.pairwise_map]
      exact (SourcePaidCaseV3.paid_distinct sound paid).imp
        (fun h he=>h (congrArg Prod.snd he))
    · intro a ha b hb
      obtain ⟨x,hx,rfl⟩:=List.mem_map.mp ha
      obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hb
      intro he
      exact Bool.noConfusion (congrArg Prod.fst he)

theorem paid_units_chronological_distinct
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PaidUnitsExec OrdExec mode T S c q out r rec chrono) :
    chrono.Pairwise (fun a b=>a.1≠b.1) :=
  (paid_units_permutation h).pairwise_iff (fun h=>Ne.symm h) |>.mpr (paid_units_distinct sound h)

theorem paid_units_slots_realize
    (h : PaidUnitsExec OrdExec mode T S c q out r rec chrono) :
    ∀ o∈rec,SlotRealizes OrdExec mode o.2 := by
  cases h with
  | @run p pr pc u us paid units =>
    intro o ho
    rcases List.mem_append.mp ho with ho|ho
    · obtain ⟨x,hx,rfl⟩:=List.mem_map.mp ho
      have hs : x.2∈(CallbackPairingAuthor.indexFrom 0 us).map Prod.snd := List.mem_map.mpr ⟨x,hx,rfl⟩
      rw [CallbackPairingAuthor.indexFrom_project] at hs
      exact SourceUnitCombineV3.combine_slots_realize units x.2 hs
    · obtain ⟨x,hx,rfl⟩:=List.mem_map.mp ho
      exact SourcePaidCaseV3.paid_slots_realize paid x hx
end SourcePaidUnitsV3
