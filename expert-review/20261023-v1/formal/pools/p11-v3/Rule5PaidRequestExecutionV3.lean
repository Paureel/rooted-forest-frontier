import Rule5CurrentExecutionV3

namespace SourceRule5PaidRequestV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open Universal233.Rule5ExecutionSource Universal233.Rule5PaidSelector SourceRule5CurrentV3
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)

def requestReturn (a : CurrentReceipt) : PaidExecutionReceipt (Option F) :=
  ⟨a.value.answer?,a.prefixWork+1,a.forestDebit,a.ordinaryCalls⟩
inductive RequestExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (j : PaidRequest) (k : Nat) : PaidExecutionReceipt (Option F)→List SourceForestV3.S→Prop
  | run (execution : CurrentExec OrdExec mode (some j.target) j.sources j.residual k a slots) :
      RequestExec OrdExec mode j k (requestReturn a) slots

def prepend (a : PaidExecutionReceipt (Option F)) (r : PaidExecutionReceipt (List F)) : PaidExecutionReceipt (List F) :=
  ⟨match a.value with | none=>r.value | some F=>F::r.value,
    a.prefixWork+r.prefixWork+3,a.forestDebit+r.forestDebit,a.ordinaryCalls++r.ordinaryCalls⟩
inductive AnswerListExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode) :
    Nat→List PaidRequest→PaidExecutionReceipt (List F)→List SourceForestV3.S→Prop
  | nil : AnswerListExec OrdExec mode k [] ⟨[],1,0,[]⟩ []
  | cons (head : RequestExec OrdExec mode j k a slots)
      (tail : AnswerListExec OrdExec mode (k+slots.length) js r ss) :
      AnswerListExec OrdExec mode k (j::js) (prepend a r) (slots++ss)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F}

theorem request_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : RequestExec OrdExec mode j k r slots) :
    r=requestAnswerMeter (ordinarySpec mode base) (fun _ _ _=>0) j := by
  cases h with
  | run execution =>
    have hv:=current_source_fields sound execution
    simp only [requestReturn,requestAnswerMeter,hv]

theorem request_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : RequestExec OrdExec mode j k r slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k r.ordinaryCalls := by
  cases h with
  | run execution =>
    have hi:=current_index sound execution
    simpa only [requestReturn] using hi

theorem list_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : AnswerListExec OrdExec mode k js r slots) :
    r=answerListMeter (ordinarySpec mode base) (fun _ _ _=>0) js := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
    have hv:=request_source_fields sound head
    simp only [answerListMeter,prepend,hv,ih]
    rfl

theorem list_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : AnswerListExec OrdExec mode k js r slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k r.ordinaryCalls := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
    have hi:=request_index sound head
    have hl:=index_length hi
    simp only [List.map_append,hi,ih,hl,prepend]
    exact (indexFrom_append _ _ _).symm

theorem request_slots_realize (h : RequestExec OrdExec mode j k r slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | run execution => exact current_slots_realize execution

theorem list_slots_realize (h : AnswerListExec OrdExec mode k js r slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  induction h with
  | nil => simp
  | cons head tail ih =>
    intro s hs
    rcases List.mem_append.mp hs with hs|hs
    · exact request_slots_realize head s hs
    · exact ih s hs

theorem request_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (j : PaidRequest) (k : Nat) : ∃ r slots,RequestExec OrdExec mode j k r slots := by
  obtain ⟨r,slots,execution⟩:=current_exists total (some j.target) j.sources j.residual k
  exact ⟨_,_,RequestExec.run execution⟩

theorem list_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (js : List PaidRequest) : ∀ k,∃ r slots,AnswerListExec OrdExec mode k js r slots := by
  induction js with
  | nil => intro k;exact ⟨_,_,AnswerListExec.nil⟩
  | cons j js ih =>
    intro k
    obtain ⟨a,slots,head⟩:=request_exists total j k
    obtain ⟨r,ss,tail⟩:=ih (k+slots.length)
    exact ⟨_,_,AnswerListExec.cons head tail⟩
end SourceRule5PaidRequestV3
