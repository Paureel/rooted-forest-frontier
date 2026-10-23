import MafCallbackExecutionV3

namespace SourceRetainedSchedulerV3
open RMAF Universal233 WholeSourceWork PaidQueries
open GenericForest.FrontierWork OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open SourceForestV3 SourceMafCallbackV3
open SourceCouplingV2 (Mode enabled Slot)
open SourceDisjointV2 (ordinarySpec)
abbrev J := Job (List Nat) F
abbrev M := MeterReceipt (List Nat) F

def resolved (c : Nat) (a : F) (r : M) : M :=
  ⟨⟨r.value.answers.map ((c,a)::·),r.value.calls,r.value.visits+1⟩,
    r.queries,r.callerWork+32,r.recursiveWork⟩
def failed (U : List Nat) (b work : Nat) : M := ⟨⟨none,[b],1⟩,[(U,b)],32,work⟩
def succeeded (U : List Nat) (b : Nat) (a : Nat×F) (work : Nat) (r : M) : M :=
  ⟨⟨r.value.answers.map (a::·),b::r.value.calls,r.value.visits+1⟩,
    (U,b)::r.queries,r.callerWork+32,work+r.recursiveWork⟩

inductive Run (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (b : Nat) : Nat→List J→M→List BothBad.Call→List Nat→List SourceForestV3.S→Prop
  | nil : Run OrdExec mode T S b k [] ⟨⟨some [],[],0⟩,[],2,0⟩ [] [] []
  | resolved (tail : Run OrdExec mode T S b k js r calls debits slots) :
      Run OrdExec mode T S b k (.resolved U c a::js) (resolved c a r) calls debits slots
  | failed (head : MafExec OrdExec mode T S U b k ret) (empty : ret.meter.value=none) :
      Run OrdExec mode T S b k (.hard U::js) (failed U b ret.meter.work) ret.calls ret.debits ret.slots
  | succeeded (head : MafExec OrdExec mode T S U b k ret) (answer : ret.meter.value=some a)
      (tail : Run OrdExec mode T S b (k+ret.slots.length) js r calls debits slots) :
      Run OrdExec mode T S b k (.hard U::js) (succeeded U b a ret.meter.work r)
        (ret.calls++calls) (ret.debits++debits) (ret.slots++slots)

def callsFrom (T S : Tree) (queries : List (List Nat×Nat)) : List BothBad.Call :=
  queries.flatMap (fun ub=>(request T S ub.1 ub.2).toList)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem run_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Run OrdExec mode T S b k js r calls debits slots) :
    r=runSourceMeter (mafRecursiveMeter (ordinarySpec mode base) T S) b js := by
  induction h with
  | nil => rfl
  | resolved tail ih => simpa only [runSourceMeter,resolved] using congrArg (resolved _ _) ih
  | failed head empty =>
    have hc:=maf_source_fields sound head
    simp only [runSourceMeter,←hc,empty,failed]
  | succeeded head answer tail ih =>
    have hc:=maf_source_fields sound head
    simpa only [runSourceMeter,←hc,answer,succeeded] using congrArg (succeeded _ _ _ _) ih

theorem run_calls (h : Run OrdExec mode T S b k js r calls debits slots) :
    calls=callsFrom T S r.queries := by
  induction h with
  | nil => rfl
  | resolved tail ih => exact ih
  | failed head empty =>
    simpa only [failed,callsFrom,List.flatMap_cons,List.flatMap_nil,List.append_nil] using maf_calls head
  | succeeded head answer tail ih =>
    simp only [succeeded,callsFrom,List.flatMap_cons]
    simp only [callsFrom] at ih
    rw [←ih,←maf_calls head]

theorem run_debits
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Run OrdExec mode T S b k js r calls debits slots) :
    debits.sum=callsForestDebit (ordinarySpec mode base) (fun _ _ _=>0) calls := by
  induction h with
  | nil => rfl
  | resolved tail ih => exact ih
  | failed head empty => exact maf_debits sound head
  | succeeded head answer tail ih =>
    have hh:=maf_debits sound head
    simp only [callsForestDebit] at hh ih
    simp only [List.sum_append,callsForestDebit,List.map_append,List.sum_append]
    rw [hh,ih]

theorem run_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Run OrdExec mode T S b k js r calls debits slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (forestQueries (ordinarySpec mode base) calls) := by
  induction h with
  | nil => rfl
  | resolved tail ih => exact ih
  | failed head empty => exact maf_index sound head
  | succeeded head answer tail ih =>
    have hi:=maf_index sound head
    have hl:=index_length hi
    rw [List.map_append,hi,ih,hl,←indexFrom_append]
    simp only [forestQueries,List.flatMap_append]

theorem run_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (b k : Nat) (js : List J) :
    ∃ r calls debits slots,Run OrdExec mode T S b k js r calls debits slots := by
  induction js generalizing k with
  | nil => exact ⟨_,_,_,_,Run.nil⟩
  | cons j js ih =>
    cases j with
    | resolved U c a =>
      obtain ⟨r,calls,debits,slots,tail⟩:=ih k
      exact ⟨_,_,_,_,Run.resolved tail⟩
    | hard U =>
      obtain ⟨ret,head⟩:=maf_exists total T S U b k
      cases he:ret.meter.value with
      | none => exact ⟨_,_,_,_,Run.failed head he⟩
      | some a =>
        obtain ⟨r,calls,debits,slots,tail⟩:=ih (k+ret.slots.length)
        exact ⟨_,_,_,_,Run.succeeded head he tail⟩

end SourceRetainedSchedulerV3
