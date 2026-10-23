import BothBadTotalityV3

namespace SourceBothBadPairV3
open RMAF Universal233 WholeSourceWork CoreWork SourceForestV3
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open SourceCouplingV2 (enabled)
open SourceDisjointV2 (ordinarySpec)

def entries (T S : Tree) (A B C : List Nat) (edge : Vertex×Vertex) (q : Nat) : List BothBad.Entry :=
  let d:=pairDescendantsMeter T edge.2
  (bothBadPlanMeter S T A B C d.value q).value

def finish (T S : Tree) (A B C : List Nat) (edge : Vertex×Vertex) (q : Nat)
    (r : SourceExecution) : SourceExecution :=
  let d:=pairDescendantsMeter T edge.2
  let p:=bothBadPlanMeter S T A B C d.value q
  ⟨r.value,d.work+p.work+r.work+12⟩

inductive PairExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : SourceCouplingV2.Mode)
    (T S : Tree) (A B C : List Nat) (edge : Vertex×Vertex) (q k : Nat) :
    SourceExecution→List Nat→List SourceForestV3.S→Prop
  | run (execution : SourceBothBadFoldV3.EntriesExec OrdExec mode T S q k
        (entries T S A B C edge q) r debits slots) :
      PairExec OrdExec mode T S A B C edge q k (finish T S A B C edge q r) debits slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : SourceCouplingV2.Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree} {A B C : List Nat}

theorem pair_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PairExec OrdExec mode T S A B C edge q k r debits slots) :
    r=bothBadLocalPairLocalSource (ordinarySpec mode base) S T A B C edge q := by
  cases h with
  | run execution =>
    have hv:=SourceBothBadFoldV3.entries_source_fields sound execution
    simp only [entries] at hv
    simp only [finish,bothBadLocalPairLocalSource,hv]

theorem pair_debits
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PairExec OrdExec mode T S A B C edge q k r debits slots) :
    debits.sum=callsForestDebit (ordinarySpec mode base) (fun _ _ _=>0) r.value.calls := by
  cases h with
  | run execution =>
    have hd:=SourceBothBadFoldV3.entries_debits sound execution
    simpa only [finish] using hd

theorem pair_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PairExec OrdExec mode T S A B C edge q k r debits slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (forestQueries (ordinarySpec mode base) r.value.calls) := by
  cases h with
  | run execution =>
    have hi:=SourceBothBadFoldV3.entries_index sound execution
    simpa only [finish] using hi

theorem pair_slots_realize (h : PairExec OrdExec mode T S A B C edge q k r debits slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | run execution => exact SourceBothBadFoldV3.entries_slots_realize execution

theorem pair_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (A B C : List Nat) (edge : Vertex×Vertex) (q k : Nat) :
    ∃ r debits slots,PairExec OrdExec mode T S A B C edge q k r debits slots := by
  obtain ⟨r,debits,slots,execution⟩:=SourceBothBadFoldV3.entries_exists total T S q (entries T S A B C edge q) k
  exact ⟨_,_,_,PairExec.run execution⟩

end SourceBothBadPairV3
