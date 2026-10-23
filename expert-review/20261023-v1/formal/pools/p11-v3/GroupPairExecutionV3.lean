import GroupEvaluationExecutionV3

namespace SourceGroupPairV3
open RMAF Universal233 WholeSourceWork CoreWork SourceForestV3
open OrdinaryDispatch.Hard2SourceWork SourceGroupEvaluationV3
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)

def outputs (T S : Tree) (A B : List Nat) (edge : Vertex×Vertex) (q : Nat) : List CoreProgram.Output :=
  let d:=pairDescendantsMeter T edge.2
  (bothBadOutputsMeter S A B d.value q).value

def finish (T S : Tree) (A B : List Nat) (edge : Vertex×Vertex) (q : Nat)
    (r : GroupEvaluationSource) : GroupPairSourceExecution :=
  let d:=pairDescendantsMeter T edge.2
  let o:=bothBadOutputsMeter S A B d.value q
  let best:=sourceBestMeter forestLengthMeter (groupedAcceptedMeter T S q) r.value.candidates
  ⟨⟨best.value,r.value.queries⟩,d.work+o.work+r.work+best.work+20⟩

inductive PairExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (A B C : List Nat) (edge : Vertex×Vertex) (q k : Nat) :
    GroupPairSourceExecution→List Nat→List SourceForestV3.S→Prop
  | run (execution : EvaluationExec OrdExec mode T S A B C q k (outputs T S A B edge q) r debits slots) :
      PairExec OrdExec mode T S A B C edge q k (finish T S A B edge q r) debits slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree} {A B C : List Nat}

theorem pair_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PairExec OrdExec mode T S A B C edge q k r debits slots) :
    r=groupPairLocalSource (ordinarySpec mode base) T S A B C edge q := by
  cases h with
  | run execution =>
    have hv:=evaluation_source_fields sound execution
    simp only [outputs] at hv
    simp only [finish,groupPairLocalSource,hv]

theorem pair_slots_realize (h : PairExec OrdExec mode T S A B C edge q k r debits slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | run execution => exact evaluation_slots_realize execution

theorem pair_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (A B C : List Nat) (edge : Vertex×Vertex) (q k : Nat) :
    ∃ r debits slots,PairExec OrdExec mode T S A B C edge q k r debits slots := by
  obtain ⟨r,debits,slots,execution⟩:=evaluation_exists total T S A B C q (outputs T S A B edge q) k
  exact ⟨_,_,_,PairExec.run execution⟩
end SourceGroupPairV3
