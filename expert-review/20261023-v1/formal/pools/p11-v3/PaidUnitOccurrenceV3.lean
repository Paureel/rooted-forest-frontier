import BothBadPairExecutionV3

namespace SourcePaidUnitOccurrenceV3
open RMAF SourceForestV3
open CallbackPairingAuthor
abbrev Occurrence := (Bool×Nat)×SourceForestV3.S

def label (paid : Bool) (slots : List SourceForestV3.S) : List Occurrence :=
  (indexFrom 0 slots).map (fun x=>((paid,x.1),x.2))

def chronological (paid units : List SourceForestV3.S) : List Occurrence :=
  label true paid++label false units

def recorded (paid units : List SourceForestV3.S) : List Occurrence :=
  label false units++label true paid

theorem two_ledger_perm (paid units : List SourceForestV3.S) :
    (chronological paid units).Perm (recorded paid units) :=
  List.perm_append_comm

def toRecorded (paid units : List SourceForestV3.S)
    (x : {o // o∈chronological paid units}) : {o // o∈recorded paid units} :=
  ⟨x.val,(two_ledger_perm paid units).mem_iff.mp x.property⟩

def toChronological (paid units : List SourceForestV3.S)
    (x : {o // o∈recorded paid units}) : {o // o∈chronological paid units} :=
  ⟨x.val,(two_ledger_perm paid units).mem_iff.mpr x.property⟩

theorem left_inverse (paid units : List SourceForestV3.S) (x : {o // o∈chronological paid units}) :
    toChronological paid units (toRecorded paid units x)=x := rfl

theorem right_inverse (paid units : List SourceForestV3.S) (x : {o // o∈recorded paid units}) :
    toRecorded paid units (toChronological paid units x)=x := rfl

theorem preserves_identity_and_slot (paid units : List SourceForestV3.S)
    (x : {o // o∈chronological paid units}) :
    (toRecorded paid units x).val.1=x.val.1 ∧ (toRecorded paid units x).val.2=x.val.2 := ⟨rfl,rfl⟩

theorem label_distinct (tag : Bool) (slots : List SourceForestV3.S) :
    (label tag slots).Pairwise (fun a b=>a.1≠b.1) := by
  simp only [label,List.pairwise_map]
  exact (indexFrom_distinct 0 slots).imp (fun h he=>h (congrArg Prod.snd he))

theorem recorded_distinct (paid units : List SourceForestV3.S) :
    (recorded paid units).Pairwise (fun a b=>a.1≠b.1) := by
  rw [recorded,List.pairwise_append]
  refine ⟨label_distinct _ _,label_distinct _ _,?_⟩
  intro a ha b hb
  obtain ⟨x,hx,rfl⟩:=List.mem_map.mp ha
  obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hb
  intro he
  have bad:=congrArg Prod.fst he
  exact Bool.noConfusion bad

theorem chronological_distinct (paid units : List SourceForestV3.S) :
    (chronological paid units).Pairwise (fun a b=>a.1≠b.1) :=
  (two_ledger_perm paid units).pairwise_iff (fun h=>Ne.symm h) |>.mpr (recorded_distinct paid units)

-- This is a sum identity for analysis weights, not a supplied runtime fee.
theorem same_sum (paid units : List SourceForestV3.S) (weight : SourceForestV3.S→Nat) :
    ((chronological paid units).map (fun o=>weight o.2)).sum=
      ((recorded paid units).map (fun o=>weight o.2)).sum :=
  ((two_ledger_perm paid units).map _).sum_nat

theorem label_project (tag : Bool) (slots : List SourceForestV3.S) :
    (label tag slots).map Prod.snd=slots := by
  simp only [label,List.map_map,Function.comp_def,indexFrom_project]

theorem query_projection (paid units : List SourceForestV3.S) :
    (recorded paid units).map (fun o=>o.2.query)=units.map SourceCouplingV2.Slot.query++paid.map SourceCouplingV2.Slot.query := by
  simp only [recorded,List.map_append]
  have hp:=congrArg (List.map SourceCouplingV2.Slot.query) (label_project true paid)
  have hu:=congrArg (List.map SourceCouplingV2.Slot.query) (label_project false units)
  simp only [List.map_map,Function.comp_def] at hp hu
  rw [hp,hu]

end SourcePaidUnitOccurrenceV3
