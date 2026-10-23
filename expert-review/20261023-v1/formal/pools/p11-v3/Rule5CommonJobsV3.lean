import PaidUnitsOccurrenceV3

namespace SourceRule5CommonJobsV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open Universal233.Rule5ExecutionSource OrdinaryCommonSplit.Caller
open SourceCouplingV2 (Mode enabled)
open SourceForestSingletonV2 (Invoke invoke_sound invoke_index)
open SourceDisjointV2 (ordinarySpec)

def prepend (j : Job) (a : Option F) (r : CommonReceipt (List (Option F))) : CommonReceipt (List (Option F)) :=
  ⟨a::r.value,r.localWork+3,0+r.recursiveWork,j::r.calls⟩

inductive JobsExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode) :
    Nat→List Job→CommonReceipt (List (Option F))→List SourceForestV3.S→Prop
  | nil : JobsExec OrdExec mode k [] ⟨[],1,0,[]⟩ []
  | cons (head : Invoke OrdExec mode k (j.T,j.S) j.budget a slot)
      (tail : JobsExec OrdExec mode (k+1) js r slots) :
      JobsExec OrdExec mode k (j::js) (prepend j a r) (slot::slots)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F}

theorem jobs_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : JobsExec OrdExec mode k js r slots) :
    r=jobsAnswersMeter (ordinarySpec mode base) (fun _ _ _=>0) js := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
    have hv:=invoke_sound head sound
    simp only [jobsAnswersMeter,prepend,hv,ih]

theorem jobs_calls (h : JobsExec OrdExec mode k js r slots) : r.calls=js := by
  induction h with
  | nil => rfl
  | cons head tail ih => simp only [prepend,ih]

theorem jobs_index (h : JobsExec OrdExec mode k js r slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (js.map (fun j=>((j.T,j.S),j.budget))) := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
    have hi:=invoke_index head
    simp only [List.map_cons,CallbackPairingAuthor.indexFrom,hi.1,hi.2,ih]

theorem jobs_slots_realize (h : JobsExec OrdExec mode k js r slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  induction h with
  | nil => simp
  | cons head tail ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl|hs
    · exact invoke_slot_realizes head
    · exact ih s hs

theorem jobs_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (js : List Job) : ∀ k,∃ r slots,JobsExec OrdExec mode k js r slots := by
  induction js with
  | nil => intro k;exact ⟨_,_,JobsExec.nil⟩
  | cons j js ih =>
    intro k
    have call : ∃ a slot,Invoke OrdExec mode k (j.T,j.S) j.budget a slot := by
      cases he:enabled mode j.budget with
      | false => exact ⟨_,_,Invoke.refused he⟩
      | true =>
        obtain ⟨a,execution⟩:=total j.T j.S j.budget he
        exact ⟨_,_,Invoke.returned he execution⟩
    obtain ⟨a,slot,head⟩:=call
    obtain ⟨r,slots,tail⟩:=ih (k+1)
    exact ⟨_,_,JobsExec.cons head tail⟩
end SourceRule5CommonJobsV3
