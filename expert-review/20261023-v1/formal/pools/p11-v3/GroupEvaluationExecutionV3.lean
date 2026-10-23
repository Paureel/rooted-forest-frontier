import GroupOutputExecutionV3

namespace SourceGroupEvaluationV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open OrdinaryDispatch.Hard2SourceWork SourceGroupOutputV3
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)

def prepend (r : Charged BothBadGrouped.OutputResult) (tail : GroupEvaluationSource) : GroupEvaluationSource :=
  let a:=groupOutputAnswerMeter r.value
  ⟨⟨a.value.toList++tail.value.candidates,r.value.trace++tail.value.queries⟩,
    r.work+a.work+tail.work+2*r.value.trace.length+20⟩

inductive EvaluationExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (A B C : List Nat) (q : Nat) :
    Nat→List CoreProgram.Output→GroupEvaluationSource→List Nat→List SourceForestV3.S→Prop
  | nil : EvaluationExec OrdExec mode T S A B C q k [] ⟨⟨[],[]⟩,2⟩ [] []
  | cons (head : OutputExec OrdExec mode T S A B C q k o r debits slots)
      (tail : EvaluationExec OrdExec mode T S A B C q (k+slots.length) os rr dd ss) :
      EvaluationExec OrdExec mode T S A B C q k (o::os) (prepend r rr) (debits++dd) (slots++ss)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree} {A B C : List Nat}

theorem evaluation_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : EvaluationExec OrdExec mode T S A B C q k os r debits slots) :
    r=groupEvaluateLocalSource (ordinarySpec mode base) T S A B C q os := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
    have hv:=output_source_fields sound head
    simp only [prepend,groupEvaluateLocalSource,hv,ih]

theorem evaluation_slots_realize (h : EvaluationExec OrdExec mode T S A B C q k os r debits slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  induction h with
  | nil => simp
  | cons head tail ih =>
    intro s hs
    rcases List.mem_append.mp hs with hs|hs
    · exact output_slots_realize head s hs
    · exact ih s hs

theorem evaluation_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (A B C : List Nat) (q : Nat) (os : List CoreProgram.Output) :
    ∀ k,∃ r debits slots,EvaluationExec OrdExec mode T S A B C q k os r debits slots := by
  induction os with
  | nil => intro k;exact ⟨_,_,_,EvaluationExec.nil⟩
  | cons o os ih =>
    intro k
    obtain ⟨r,debits,slots,head⟩:=output_exists total T S A B C q k o
    obtain ⟨rr,dd,ss,tail⟩:=ih (k+slots.length)
    exact ⟨_,_,_,EvaluationExec.cons head tail⟩
end SourceGroupEvaluationV3
