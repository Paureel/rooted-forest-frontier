import RetainedSchedulerV3

namespace SourceOrdinaryLocalV3
open RMAF Universal233 WholeSourceWork PaidQueries
open GenericForest.FrontierWork OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open SourceForestV3 SourceMafCallbackV3
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)
open SourceRetainedSchedulerV3 (M J callsFrom)

theorem queries_value (T S : Tree) (qs : List (List Nat×Nat)) :
    (ordinaryQueriesMeter T S qs).value=callsFrom T S qs := by
  induction qs with
  | nil => rfl
  | cons ub qs ih =>
    simp only [ordinaryQueriesMeter,callsFrom,List.flatMap_cons] at ih ⊢
    rw [ih]
    rfl

def finish (T S : Tree) (Q : List (List Nat)) (r : M) : SourceExecution :=
  let prep:=ordinaryPrepareMeter T S Q
  let f:=optionFlattenMeter r.value.answers
  let qs:=ordinaryQueriesMeter T S r.queries
  ⟨⟨f.value,qs.value⟩,prep.work+r.callerWork+r.recursiveWork+f.work+qs.work+16⟩

inductive LocalExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (Q : List (List Nat)) (b k : Nat) :
    SourceExecution→List Nat→List SourceForestV3.S→Prop
  | refused (none : (ordinaryPrepareMeter T S Q).value=none) :
      LocalExec OrdExec mode T S Q b k ⟨⟨Option.none,[]⟩,(ordinaryPrepareMeter T S Q).work+4⟩ [] []
  | prepared (some : (ordinaryPrepareMeter T S Q).value=some js)
      (execution : SourceRetainedSchedulerV3.Schedule OrdExec mode T S b js k r calls debits slots) :
      LocalExec OrdExec mode T S Q b k (finish T S Q r) debits slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree} {Q : List (List Nat)}

theorem local_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : LocalExec OrdExec mode T S Q b k r debits slots) :
    r=ordinaryLocalSource (ordinarySpec mode base) T S Q b := by
  cases h with
  | refused none => simp only [ordinaryLocalSource,none,finish]
  | prepared some execution =>
    have hr:=SourceRetainedSchedulerV3.schedule_source_fields sound execution
    simp only [ordinaryLocalSource,some,finish,hr]

theorem local_debits
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : LocalExec OrdExec mode T S Q b k r debits slots) :
    debits.sum=callsForestDebit (ordinarySpec mode base) (fun _ _ _=>0) r.value.calls := by
  cases h with
  | refused none => rfl
  | prepared some execution =>
    have hd:=SourceRetainedSchedulerV3.schedule_debits sound execution
    have hc:=SourceRetainedSchedulerV3.schedule_calls execution
    simpa only [finish,queries_value,←hc] using hd

theorem local_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : LocalExec OrdExec mode T S Q b k r debits slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (forestQueries (ordinarySpec mode base) r.value.calls) := by
  cases h with
  | refused none => rfl
  | prepared some execution =>
    have hi:=SourceRetainedSchedulerV3.schedule_index sound execution
    have hc:=SourceRetainedSchedulerV3.schedule_calls execution
    simpa only [finish,queries_value,←hc] using hi

theorem local_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (Q : List (List Nat)) (b k : Nat) :
    ∃ r debits slots,LocalExec OrdExec mode T S Q b k r debits slots := by
  cases hp:(ordinaryPrepareMeter T S Q).value with
  | none => exact ⟨_,_,_,LocalExec.refused hp⟩
  | some js =>
    obtain ⟨r,calls,debits,slots,execution⟩:=SourceRetainedSchedulerV3.schedule_exists total T S b k js
    exact ⟨_,_,_,LocalExec.prepared hp execution⟩

end SourceOrdinaryLocalV3
