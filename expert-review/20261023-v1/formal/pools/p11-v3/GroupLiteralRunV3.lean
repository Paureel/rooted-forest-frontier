import GroupCallbackExecutionV3

namespace SourceGroupLiteralV3
open RMAF Universal233 WholeSourceWork PaidQueries SourceForestV3
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open GenericForest.FrontierWork Universal233.GroupedFullQuery SourceGroupCallbackV3
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)
abbrev Receipt := LiteralReceiptSource Problem F
abbrev J := Job Problem F

def resolved (c : Nat) (a : F) (r : Receipt) : Receipt :=
  ⟨⟨⟨r.value.value.answers.map ((c,a)::·),r.value.value.calls,r.value.value.visits+1⟩,
    r.value.queries,r.value.callerWork+5,r.value.recursiveWork⟩,r.localWork+32,r.callbackWork⟩
def failed (p : Problem) (b : Nat) (a : Charged (Option (Nat×F))) : Receipt :=
  ⟨⟨⟨none,[b],1⟩,[(p,b)],8,0⟩,32,a.work⟩
def succeeded (p : Problem) (b : Nat) (a : Charged (Option (Nat×F))) (x : Nat×F) (r : Receipt) : Receipt :=
  ⟨⟨⟨r.value.value.answers.map (x::·),b::r.value.value.calls,r.value.value.visits+1⟩,
    (p,b)::r.value.queries,r.value.callerWork+8,r.value.recursiveWork⟩,r.localWork+32,a.work+r.callbackWork⟩

inductive Run (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode) (b : Nat) :
    Nat→List J→Receipt→List Nat→List SourceForestV3.S→Prop
  | nil : Run OrdExec mode b k [] ⟨⟨⟨some [],[],0⟩,[],2,0⟩,2,0⟩ [] []
  | resolved (tail : Run OrdExec mode b k js r debits slots) :
      Run OrdExec mode b k (.resolved p c a::js) (resolved c a r) debits slots
  | failed (head : CallbackExec OrdExec mode p b k a debit slots) (empty : a.value=none) :
      Run OrdExec mode b k (.hard p::js) (failed p b a) [debit] slots
  | succeeded (head : CallbackExec OrdExec mode p b k a debit slots) (answer : a.value=some x)
      (tail : Run OrdExec mode b (k+slots.length) js r debits ss) :
      Run OrdExec mode b k (.hard p::js) (succeeded p b a x r) (debit::debits) (slots++ss)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F}

theorem run_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Run OrdExec mode b k js r debits slots) :
    r=literalRunSource (groupCallbackMeter (ordinarySpec mode base)) b js := by
  induction h with
  | nil => rfl
  | resolved tail ih => simp only [resolved,literalRunSource,ih]
  | failed head empty =>
    have hv:=callback_fields sound head
    simp only [literalRunSource,←hv,empty,failed]
  | succeeded head answer tail ih =>
    have hv:=callback_fields sound head
    simp only [literalRunSource,←hv,answer,←ih,succeeded]

theorem run_debits
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Run OrdExec mode b k js r debits slots) :
    debits.sum=callsForestDebit (ordinarySpec mode base) (fun _ _ _=>0) (groupCalls r.value.queries) := by
  induction h with
  | nil => rfl
  | resolved tail ih => exact ih
  | failed head empty =>
    have hd:=callback_debit sound head
    simpa only [failed,groupCalls,List.map_cons,List.map_nil,callsForestDebit,List.sum_cons,List.sum_nil,Nat.add_zero] using hd
  | succeeded head answer tail ih =>
    have hd:=callback_debit sound head
    simp only [List.sum_cons,succeeded,groupCalls,List.map_cons,callsForestDebit,List.sum_cons] at ih ⊢
    rw [hd,ih]

theorem run_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Run OrdExec mode b k js r debits slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (forestQueries (ordinarySpec mode base) (groupCalls r.value.queries)) := by
  induction h with
  | nil => rfl
  | resolved tail ih => exact ih
  | failed head empty =>
    simpa only [failed,groupCalls,List.map_cons,List.map_nil,forestQueries,List.flatMap_cons,List.flatMap_nil,List.append_nil] using callback_index sound head
  | @succeeded k p a debit slots x js r debits ss head answer tail ih =>
    have hi:=callback_index sound head
    have hl:=index_length hi
    simp only [List.map_append,hi,ih,hl,succeeded,groupCalls,List.map_cons,forestQueries,List.flatMap_cons]
    exact (indexFrom_append _ _ _).symm

theorem run_slots_realize (h : Run OrdExec mode b k js r debits slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  induction h with
  | nil => simp
  | resolved tail ih => exact ih
  | failed head empty => exact callback_slots_realize head
  | succeeded head answer tail ih =>
    intro s hs
    rcases List.mem_append.mp hs with hs|hs
    · exact callback_slots_realize head s hs
    · exact ih s hs

theorem run_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (b : Nat) (js : List J) : ∀ k,∃ r debits slots,Run OrdExec mode b k js r debits slots := by
  induction js with
  | nil => intro k;exact ⟨_,_,_,Run.nil⟩
  | cons j js ih =>
    intro k
    cases j with
    | resolved p c a =>
      obtain ⟨r,debits,slots,tail⟩:=ih k
      exact ⟨_,_,_,Run.resolved tail⟩
    | hard p =>
      obtain ⟨a,debit,slots,head⟩:=callback_exists total p b k
      cases he:a.value with
      | none => exact ⟨_,_,_,Run.failed head he⟩
      | some x =>
        obtain ⟨r,debits,ss,tail⟩:=ih (k+slots.length)
        exact ⟨_,_,_,Run.succeeded head he tail⟩
end SourceGroupLiteralV3
