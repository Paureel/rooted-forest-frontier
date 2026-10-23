import RetainedSchedulerRunV3

namespace SourceRetainedSchedulerV3
open RMAF Universal233 WholeSourceWork PaidQueries
open GenericForest.FrontierWork OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open SourceForestV3 SourceMafCallbackV3
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)

def scheduled (q : Nat) (js : List J) (r : M) : M :=
  let k:=knownCostMeter js
  let p:=pendingMeter js
  let b:=allocatedMeter q js
  let a:=acceptAnswersMeter q r.value.answers
  let pc:=postChargeMeter r.value
  ⟨⟨a.value,r.value.calls,r.value.visits⟩,r.queries,
    k.work+p.work+b.work+r.callerWork+a.work+pc.work+js.length+40,r.recursiveWork⟩

inductive Schedule (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (q : Nat) (js : List J) (k : Nat) :
    M→List BothBad.Call→List Nat→List SourceForestV3.S→Prop
  | refused (small : q<(knownCostMeter js).value+2*(pendingMeter js).value) :
      Schedule OrdExec mode T S q js k
        ⟨⟨none,[],0⟩,[],(knownCostMeter js).work+(pendingMeter js).work+js.length+24,0⟩ [] [] []
  | run (enough : ¬q<(knownCostMeter js).value+2*(pendingMeter js).value)
      (execution : Run OrdExec mode T S (allocatedMeter q js).value k js r calls debits slots) :
      Schedule OrdExec mode T S q js k (scheduled q js r) calls debits slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem schedule_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Schedule OrdExec mode T S q js k r calls debits slots) :
    r=scheduleSourceMeter (mafRecursiveMeter (ordinarySpec mode base) T S) q js := by
  cases h with
  | refused small => simp only [scheduleSourceMeter,small,↓reduceIte]
  | run enough execution =>
    have hr:=run_source_fields sound execution
    simpa only [scheduleSourceMeter,enough,↓reduceIte,scheduled] using congrArg (scheduled q js) hr

theorem schedule_calls (h : Schedule OrdExec mode T S q js k r calls debits slots) :
    calls=callsFrom T S r.queries := by
  cases h with
  | refused small => rfl
  | run enough execution => simpa only [scheduled] using run_calls execution

theorem schedule_debits
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Schedule OrdExec mode T S q js k r calls debits slots) :
    debits.sum=callsForestDebit (ordinarySpec mode base) (fun _ _ _=>0) calls := by
  cases h with
  | refused small => rfl
  | run enough execution => exact run_debits sound execution

theorem schedule_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Schedule OrdExec mode T S q js k r calls debits slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (forestQueries (ordinarySpec mode base) calls) := by
  cases h with
  | refused small => rfl
  | run enough execution => exact run_index sound execution

theorem schedule_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (q k : Nat) (js : List J) :
    ∃ r calls debits slots,Schedule OrdExec mode T S q js k r calls debits slots := by
  by_cases small:q<(knownCostMeter js).value+2*(pendingMeter js).value
  · exact ⟨_,_,_,_,Schedule.refused small⟩
  · obtain ⟨r,calls,debits,slots,execution⟩:=run_exists total T S (allocatedMeter q js).value k js
    exact ⟨_,_,_,_,Schedule.run small execution⟩

end SourceRetainedSchedulerV3
