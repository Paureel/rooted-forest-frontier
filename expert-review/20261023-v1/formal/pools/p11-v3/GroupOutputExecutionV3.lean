import GroupLiteralScheduleV3

namespace SourceGroupOutputV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open OrdinaryDispatch.Hard2SourceWork
open Universal233.GroupedFullQuery SourceGroupLiteralV3
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)

def finish (T S : Tree) (A B C : List Nat) (o : CoreProgram.Output) (r : Receipt) :
    Charged BothBadGrouped.OutputResult :=
  let j:=groupJobsForMeter T S A B C o
  ⟨.scheduled r.value,2*o.sourceCuts.length+j.work+r.localWork+r.callbackWork+20⟩

inductive OutputExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (A B C : List Nat) (q k : Nat) (o : CoreProgram.Output) :
    Charged BothBadGrouped.OutputResult→List Nat→List SourceForestV3.S→Prop
  | unaffordable (over : ¬o.sourceCuts.length≤q) :
      OutputExec OrdExec mode T S A B C q k o ⟨.unaffordable,o.sourceCuts.length+8⟩ [] []
  | refused (paid : o.sourceCuts.length≤q) (empty : (groupJobsForMeter T S A B C o).value=none) :
      OutputExec OrdExec mode T S A B C q k o
        ⟨.refused,2*o.sourceCuts.length+(groupJobsForMeter T S A B C o).work+12⟩ [] []
  | scheduled (paid : o.sourceCuts.length≤q) (found : (groupJobsForMeter T S A B C o).value=some js)
      (execution : Schedule OrdExec mode (q-o.sourceCuts.length) js k r debits slots) :
      OutputExec OrdExec mode T S A B C q k o (finish T S A B C o r) debits slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree} {A B C : List Nat}

theorem output_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : OutputExec OrdExec mode T S A B C q k o r debits slots) :
    r=groupRunOutputLocalSource (ordinarySpec mode base) T S A B C q o := by
  cases h with
  | unaffordable over => simp only [groupRunOutputLocalSource,over,↓reduceIte]
  | refused paid empty => simp only [groupRunOutputLocalSource,paid,↓reduceIte,empty]
  | scheduled paid found execution =>
    have hv:=schedule_source_fields sound execution
    simp only [groupRunOutputLocalSource,paid,↓reduceIte,found,finish,hv]

theorem output_slots_realize (h : OutputExec OrdExec mode T S A B C q k o r debits slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | unaffordable over => simp
  | refused paid empty => simp
  | scheduled paid found execution => exact schedule_slots_realize execution

theorem output_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (A B C : List Nat) (q k : Nat) (o : CoreProgram.Output) :
    ∃ r debits slots,OutputExec OrdExec mode T S A B C q k o r debits slots := by
  by_cases paid:o.sourceCuts.length≤q
  · cases hp:(groupJobsForMeter T S A B C o).value with
    | none => exact ⟨_,_,_,OutputExec.refused paid hp⟩
    | some js =>
      obtain ⟨r,debits,slots,execution⟩:=schedule_exists total (q-o.sourceCuts.length) js k
      exact ⟨_,_,_,OutputExec.scheduled paid hp execution⟩
  · exact ⟨_,_,_,OutputExec.unaffordable paid⟩
end SourceGroupOutputV3
