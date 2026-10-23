import PaidCaseOccurrenceV3

namespace SourcePaidUnitsV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.OuterSource
open OrdinaryDispatch.CompleteSource
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)
abbrev Occurrence := (Bool×(Nat×Nat))×SourceForestV3.S

def labelPaid (xs : List SourcePaidCaseV3.Occurrence) : List Occurrence :=
  xs.map (fun o=>((true,o.1),o.2))
def labelUnits (xs : List SourceForestV3.S) : List Occurrence :=
  (CallbackPairingAuthor.indexFrom 0 xs).map (fun o=>((false,(0,o.1)),o.2))
def recorded (paid : List SourcePaidCaseV3.Occurrence) (units : List SourceForestV3.S) :=
  labelUnits units++labelPaid paid
def chronological (paid : List SourcePaidCaseV3.Occurrence) (units : List SourceForestV3.S) :=
  labelPaid paid++labelUnits units

def finish (p units : SourceExecution) : Charged (Option F) :=
  ⟨units.value.answer,p.work+units.work+2⟩

inductive PaidUnitsExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Hard2Overlap.Result) :
    Charged (Option F)→List Occurrence→List Occurrence→Prop
  | run (paid : SourcePaidCaseV3.PaidExec OrdExec mode T S c q out p pr pc)
      (units : SourceUnitCombineV3.CombineExec OrdExec mode T S c.a c.b q p.value 0 u us) :
      PaidUnitsExec OrdExec mode T S c q out (finish p u) (recorded pr us) (chronological pc us)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem paid_units_permutation
    (h : PaidUnitsExec OrdExec mode T S c q out r rec chrono) : chrono.Perm rec := by
  cases h with
  | run paid units =>
    have hp:=(SourcePaidCaseV3.paid_permutation paid).map (fun o=>((true,o.1),o.2))
    exact (hp.append_right _).trans List.perm_append_comm

theorem paid_units_queries
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PaidUnitsExec OrdExec mode T S c q out r rec chrono) :
    ∃ calls,rec.map (fun o=>o.2.query)=forestQueries (ordinarySpec mode base) calls ∧
      calls=(combineSource (ordinarySpec mode base) (fun _ _ _=>0) T S c.a c.b q
        (paidCaseCompleteSource (ordinarySpec mode base) (fun _ _ _=>0) T S c q out).value).value.calls := by
  cases h with
  | @run p pr pc u us paid units =>
    have hp:=SourcePaidCaseV3.paid_query_projection sound paid
    have hu:=SourceUnitCombineV3.combine_unit_index sound units
    have hup:=congrArg (List.map Prod.snd) hu
    simp only [List.map_map,Function.comp_def,CallbackPairingAuthor.indexFrom_project] at hup
    have hpf:=SourcePaidCaseV3.paid_source_fields sound paid
    refine ⟨_,?_,rfl⟩
    simp only [combineSource,forestQueries,List.flatMap_append,recorded,labelPaid,labelUnits,List.map_append,List.map_map,
      Function.comp_def,CallbackPairingAuthor.indexFrom_project]
    have hz:=congrArg (List.map SourceCouplingV2.Slot.query) (CallbackPairingAuthor.indexFrom_project 0 us)
    simp only [List.map_map,Function.comp_def] at hz
    rw [hz,hup,hp,hpf]

theorem paid_units_complete_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=OrdinaryDispatch.FastOrdinary.solve b T S)
    (h : PaidUnitsExec OrdExec (.cutoff q) T S c q out r rec chrono) :
    r=completeRouteSource (fun _ _ _=>0) T S c q (.paid out) := by
  cases h with
  | run paid units =>
    have hp:=SourcePaidCaseV3.paid_source_fields (base:=fun T S b=>OrdinaryDispatch.FastOrdinary.solve b T S) sound paid
    have hu:=SourceUnitCombineV3.combine_source_fields (base:=fun T S b=>OrdinaryDispatch.FastOrdinary.solve b T S) sound units
    rw [cutoff_spec] at hp hu
    simp only [completeRouteSource,finish,←hp,hu]

theorem paid_units_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Hard2Overlap.Result) :
    ∃ r rec chrono,PaidUnitsExec OrdExec mode T S c q out r rec chrono := by
  obtain ⟨p,pr,pc,paid⟩:=SourcePaidCaseV3.paid_exists total T S c q out
  obtain ⟨u,us,units⟩:=SourceUnitCombineV3.combine_exists total T S c.a c.b q 0 p.value
  exact ⟨_,_,_,PaidUnitsExec.run paid units⟩

def toRecorded (h : PaidUnitsExec OrdExec mode T S c q out r rec chrono)
    (x : {o // o∈chrono}) : {o // o∈rec} := ⟨x.val,(paid_units_permutation h).mem_iff.mp x.property⟩
def toChronological (h : PaidUnitsExec OrdExec mode T S c q out r rec chrono)
    (x : {o // o∈rec}) : {o // o∈chrono} := ⟨x.val,(paid_units_permutation h).mem_iff.mpr x.property⟩
theorem left_inverse (h : PaidUnitsExec OrdExec mode T S c q out r rec chrono) (x : {o // o∈chrono}) :
    toChronological h (toRecorded h x)=x := rfl
theorem right_inverse (h : PaidUnitsExec OrdExec mode T S c q out r rec chrono) (x : {o // o∈rec}) :
    toRecorded h (toChronological h x)=x := rfl
theorem preserves_every_slot_field (h : PaidUnitsExec OrdExec mode T S c q out r rec chrono) (x : {o // o∈chrono}) :
    (toRecorded h x).val=x.val := rfl
theorem same_sum (h : PaidUnitsExec OrdExec mode T S c q out r rec chrono) (weight : SourceForestV3.S→Nat) :
    (chrono.map (fun o=>weight o.2)).sum=(rec.map (fun o=>weight o.2)).sum :=
  ((paid_units_permutation h).map _).sum_nat
end SourcePaidUnitsV3
