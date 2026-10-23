import GroupLiteralRunV3

namespace SourceGroupLiteralV3
open RMAF Universal233 WholeSourceWork PaidQueries SourceForestV3
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open GenericForest.FrontierWork Universal233.GroupedFullQuery
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)

def finishSchedule (q : Nat) (js : List J) (r : Receipt) : Receipt :=
  let k:=knownCostMeter js
  let p:=pendingMeter js
  let b:=allocatedMeter q js
  let a:=acceptAnswersMeter q r.value.value.answers
  let pc:=postChargeMeter r.value.value
  ⟨⟨⟨a.value,r.value.value.calls,r.value.value.visits⟩,r.value.queries,
      16*js.length+20+r.value.callerWork+pc.value,r.value.recursiveWork⟩,
    k.work+p.work+b.work+r.localWork+a.work+pc.work+js.length+40,r.callbackWork⟩

inductive Schedule (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (q : Nat) (js : List J) (k : Nat) : Receipt→List Nat→List SourceForestV3.S→Prop
  | refused (small : q<(knownCostMeter js).value+2*(pendingMeter js).value) :
      Schedule OrdExec mode q js k
        ⟨⟨⟨none,[],0⟩,[],8*js.length+8,0⟩,
          (knownCostMeter js).work+(pendingMeter js).work+js.length+24,0⟩ [] []
  | run (enough : ¬q<(knownCostMeter js).value+2*(pendingMeter js).value)
      (execution : Run OrdExec mode (allocatedMeter q js).value k js r debits slots) :
      Schedule OrdExec mode q js k (finishSchedule q js r) debits slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F}

theorem schedule_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Schedule OrdExec mode q js k r debits slots) :
    r=literalScheduleSource (groupCallbackMeter (ordinarySpec mode base)) q js := by
  cases h with
  | refused small => simp only [literalScheduleSource,small,↓reduceIte]
  | run enough execution =>
    have hv:=run_source_fields sound execution
    simp only [literalScheduleSource,enough,↓reduceIte,finishSchedule,hv]

theorem schedule_debits
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Schedule OrdExec mode q js k r debits slots) :
    debits.sum=callsForestDebit (ordinarySpec mode base) (fun _ _ _=>0) (groupCalls r.value.queries) := by
  cases h with
  | refused small => rfl
  | run enough execution =>
    have hd:=run_debits sound execution
    simpa only [finishSchedule] using hd

theorem schedule_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Schedule OrdExec mode q js k r debits slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (forestQueries (ordinarySpec mode base) (groupCalls r.value.queries)) := by
  cases h with
  | refused small => rfl
  | run enough execution =>
    have hi:=run_index sound execution
    simpa only [finishSchedule] using hi

theorem schedule_slots_realize (h : Schedule OrdExec mode q js k r debits slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | refused small => simp
  | run enough execution => exact run_slots_realize execution

theorem schedule_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (q : Nat) (js : List J) (k : Nat) :
    ∃ r debits slots,Schedule OrdExec mode q js k r debits slots := by
  by_cases small:q<(knownCostMeter js).value+2*(pendingMeter js).value
  · exact ⟨_,_,_,Schedule.refused small⟩
  · obtain ⟨r,debits,slots,execution⟩:=run_exists total (allocatedMeter q js).value js k
    exact ⟨_,_,_,Schedule.run small execution⟩
end SourceGroupLiteralV3
