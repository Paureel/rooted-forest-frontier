import Rule5PaidRequestExecutionV3

namespace SourceRule5PaidSelectionV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open Universal233.Rule5ExecutionSource Universal233.Rule5PaidSelector
open Universal233.Rule5RemainingLocalWork Universal233.Rule5SelectedLocalWork
open Universal233.ClassifierCheckFee Universal233.PaidLiteralDecisionWork
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)

def answersReturn {T S : Tree} (R : SelectedPaid T S) (q : Nat)
    (r : PaidExecutionReceipt (List F)) : PaidExecutionReceipt (List F) :=
  ⟨r.value,(requestsMeter R.geometry q).work+r.prefixWork+2,r.forestDebit,r.ordinaryCalls⟩
inductive AnswersExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    {T S : Tree} (R : SelectedPaid T S) (q k : Nat) : PaidExecutionReceipt (List F)→List SourceForestV3.S→Prop
  | run (execution : SourceRule5PaidRequestV3.AnswerListExec OrdExec mode k (requestsMeter R.geometry q).value r slots) :
      AnswersExec OrdExec mode R q k (answersReturn R q r) slots

def bestReturn (T S : Tree) (q : Nat) (a : PaidExecutionReceipt (List F)) : PaidExecutionReceipt (Option F) :=
  let b:=bestLengthMeter (originalAcceptedMeter T S q) a.value
  ⟨b.value,a.prefixWork+b.work+a.value.length+2,a.forestDebit,a.ordinaryCalls⟩
inductive BestExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    {T S : Tree} (R : SelectedPaid T S) (q k : Nat) : PaidExecutionReceipt (Option F)→List SourceForestV3.S→Prop
  | run (execution : AnswersExec OrdExec mode R q k r slots) :
      BestExec OrdExec mode R q k (bestReturn T S q r) slots

def prepare (T S : Tree) (a b : Nat) :=paidSelectedMeter checkFee (literalFee T S a b) T S a b

def solvedReturn (T S : Tree) (a b : Nat) (r : PaidExecutionReceipt (Option F)) : PaidExecutionReceipt Rule5PaidOrdinary.SelectedResult :=
  ⟨.answered r.value,(prepare T S a b).work+r.prefixWork+2,r.forestDebit,r.ordinaryCalls⟩
inductive SolvedExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (a b q k : Nat) : PaidExecutionReceipt Rule5PaidOrdinary.SelectedResult→List SourceForestV3.S→Prop
  | refused (empty : (prepare T S a b).value=none) :
      SolvedExec OrdExec mode T S a b q k ⟨.builderRefused,(prepare T S a b).work+2,0,[]⟩ []
  | built (found : (prepare T S a b).value=some R) (execution : BestExec OrdExec mode R q k r slots) :
      SolvedExec OrdExec mode T S a b q k (solvedReturn T S a b r) slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem answers_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : AnswersExec OrdExec mode R q k r slots) :
    r=answersMeter (ordinarySpec mode base) (fun _ _ _=>0) R q := by
  cases h with
  | run execution =>
    have hv:=SourceRule5PaidRequestV3.list_source_fields sound execution
    simp only [answersMeter,answersReturn,hv]

theorem best_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : BestExec OrdExec mode R q k r slots) :
    r=bestForMeter (ordinarySpec mode base) (fun _ _ _=>0) R q := by
  cases h with
  | run execution =>
    have hv:=answers_source_fields sound execution
    simp only [bestForMeter,bestReturn,hv]

theorem solved_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : SolvedExec OrdExec mode T S a b q k r slots) :
    r=solveSelectedMeter (ordinarySpec mode base) (fun _ _ _=>0) checkFee (literalFee T S a b) T S a b q := by
  cases h with
  | refused empty =>
    simp only [prepare] at empty ⊢
    simp only [solveSelectedMeter,empty]
  | built found execution =>
    have hv:=best_source_fields sound execution
    simp only [prepare] at found
    simp only [solveSelectedMeter,found,solvedReturn,prepare,hv]

def sourceView (r : PaidExecutionReceipt Rule5PaidOrdinary.SelectedResult) : Charged Rule5PaidOrdinary.SelectedResult :=
  ⟨r.value,r.prefixWork+r.forestDebit⟩
theorem solved_source_view
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : SolvedExec OrdExec mode T S a b q k r slots) :
    sourceView r=paidSelectedSource (ordinarySpec mode base) (fun _ _ _=>0) checkFee (literalFee T S a b) T S a b q := by
  simp only [sourceView,paidSelectedSource,←solved_source_fields sound h]

theorem answers_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : AnswersExec OrdExec mode R q k r slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k r.ordinaryCalls := by
  cases h with
  | run execution =>
    have hi:=SourceRule5PaidRequestV3.list_index sound execution
    simpa only [answersReturn] using hi

theorem best_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : BestExec OrdExec mode R q k r slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k r.ordinaryCalls := by
  cases h with
  | run execution =>
    have hi:=answers_index sound execution
    simpa only [bestReturn] using hi

theorem solved_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : SolvedExec OrdExec mode T S a b q k r slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k r.ordinaryCalls := by
  cases h with
  | refused empty => rfl
  | built found execution =>
    have hi:=best_index sound execution
    simpa only [solvedReturn] using hi

theorem answers_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (R : SelectedPaid T S) (q k : Nat) : ∃ r slots,AnswersExec OrdExec mode R q k r slots := by
  obtain ⟨r,slots,execution⟩:=SourceRule5PaidRequestV3.list_exists total (requestsMeter R.geometry q).value k
  exact ⟨_,_,AnswersExec.run execution⟩

theorem best_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (R : SelectedPaid T S) (q k : Nat) : ∃ r slots,BestExec OrdExec mode R q k r slots := by
  obtain ⟨r,slots,execution⟩:=answers_exists total R q k
  exact ⟨_,_,BestExec.run execution⟩

theorem solved_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (a b q k : Nat) : ∃ r slots,SolvedExec OrdExec mode T S a b q k r slots := by
  cases hp:(prepare T S a b).value with
  | none => exact ⟨_,_,SolvedExec.refused hp⟩
  | some R =>
    obtain ⟨r,slots,execution⟩:=best_exists total R q k
    exact ⟨_,_,SolvedExec.built hp execution⟩

theorem answers_slots_realize (h : AnswersExec OrdExec mode R q k r slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | run execution => exact SourceRule5PaidRequestV3.list_slots_realize execution

theorem best_slots_realize (h : BestExec OrdExec mode R q k r slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | run execution => exact answers_slots_realize execution

theorem solved_slots_realize (h : SolvedExec OrdExec mode T S a b q k r slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | refused empty => simp
  | built found execution => exact best_slots_realize execution
end SourceRule5PaidSelectionV3
