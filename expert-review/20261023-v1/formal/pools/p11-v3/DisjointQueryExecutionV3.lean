import OrdinaryLocalExecutionV3

namespace SourceDisjointQueryV3
open RMAF Universal233 WholeSourceWork
open GenericForest.FrontierWork OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open SourceForestV3 SourceOrdinaryLocalV3
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)

def finish (T S : Tree) (parts : List (List Nat)) (q : Nat) (r : SourceExecution)
    (debits : List Nat) : SourceExecution :=
  let check:=checkedMeter T S q r.value.answer
  ⟨⟨check.value,r.value.calls⟩,(parts.length+r.work+check.work+16)+debits.sum⟩

inductive QueryExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (parts : List (List Nat)) (q k : Nat) :
    SourceExecution→List SourceForestV3.S→Prop
  | refused (over : ¬parts.length-1≤q) :
      QueryExec OrdExec mode T S parts q k ⟨⟨none,[]⟩,parts.length+8+0⟩ []
  | returned (paid : parts.length-1≤q)
      (execution : LocalExec OrdExec mode T S parts (q-(parts.length-1)) k r debits slots) :
      QueryExec OrdExec mode T S parts q k (finish T S parts q r debits) slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem query_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : QueryExec OrdExec mode T S parts q k r slots) :
    r=disjointQuerySource (ordinarySpec mode base) (fun _ _ _=>0) T S parts q := by
  cases h with
  | refused over =>
    simp only [disjointQuerySource,disjointQueryLocalSource,over,↓reduceIte,callsForestDebit,
      List.map_nil,List.sum_nil]
  | returned paid execution =>
    have hr:=local_source_fields sound execution
    have hd:=local_debits sound execution
    simp only [disjointQuerySource,disjointQueryLocalSource,paid,↓reduceIte]
    rw [←hr,←hd]
    rfl

theorem query_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : QueryExec OrdExec mode T S parts q k r slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (forestQueries (ordinarySpec mode base) r.value.calls) := by
  cases h with
  | refused over => rfl
  | returned paid execution => simpa only [finish] using local_index sound execution

theorem query_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (parts : List (List Nat)) (q k : Nat) :
    ∃ r slots,QueryExec OrdExec mode T S parts q k r slots := by
  by_cases paid:parts.length-1≤q
  · obtain ⟨r,debits,slots,execution⟩:=local_exists total T S parts (q-(parts.length-1)) k
    exact ⟨_,_,QueryExec.returned paid execution⟩
  · exact ⟨_,_,QueryExec.refused paid⟩

end SourceDisjointQueryV3
