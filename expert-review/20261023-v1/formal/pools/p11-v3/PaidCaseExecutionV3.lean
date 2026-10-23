import BadPairExecutionV3

namespace SourcePaidCaseV3
open RMAF Universal233 WholeSourceWork CoreWork SourceForestV3
open GenericForest.FrontierWork
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.OuterSource
open OrdinaryDispatch.CompleteSource
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)
abbrev Occurrence := (Nat×Nat)×SourceForestV3.S

def linear (slots : List SourceForestV3.S) : List Occurrence :=
  slots.map (fun s=>((0,s.index),s))

inductive SelectedExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Hard2Overlap.Result) :
    PaidRoute→SourceExecution→List Occurrence→List Occurrence→Prop
  | empty : SelectedExec OrdExec mode T S c q out .empty ⟨⟨none,[]⟩,0⟩ [] []
  | good (A B C : List Nat) (execution : SourceGoodPairV3.GoodExec OrdExec mode T S A B C q r slots) :
      SelectedExec OrdExec mode T S c q out (.good A B C) r (linear slots) (linear slots)
  | hard (execution : SourceFullOutputsV3.HardPaidExec OrdExec mode T S q c out r cells) :
      SelectedExec OrdExec mode T S c q out .hard r
        (SourceFullOutputsV3.recorded cells) (SourceFullOutputsV3.chronological cells)
  | bad (A B C : List Nat) (execution : SourceBadPairV3.LocalExec OrdExec mode T S A B C edge q 0 r debits slots) :
      SelectedExec OrdExec mode T S c q out (.bad A B C edge) (SourceBadPairV3.complete r debits)
        (linear slots) (linear slots)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem selected_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : SelectedExec OrdExec mode T S c q out route r recorded chronological) :
    r=selectedPaidSource (ordinarySpec mode base) (fun _ _ _=>0) T S c q out route := by
  cases h with
  | empty => rfl
  | good A B C execution => exact SourceGoodPairV3.good_source_fields sound execution
  | hard execution => exact SourceFullOutputsV3.hardPaid_source_fields sound execution
  | bad A B C execution => exact SourceBadPairV3.bad_source_fields sound execution

theorem selected_query_projection
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : SelectedExec OrdExec mode T S c q out route r recorded chronological) :
    recorded.map (fun o=>o.2.query)=forestQueries (ordinarySpec mode base) r.value.calls := by
  cases h with
  | empty => rfl
  | good A B C execution =>
    have hi:=SourceGoodPairV3.good_index sound execution
    have hp:=congrArg (List.map Prod.snd) hi
    simpa only [linear,List.map_map,Function.comp_def,CallbackPairingAuthor.indexFrom_project] using hp
  | hard execution =>
    cases execution with
    | run outputs =>
      have hp:=SourceFullOutputsV3.recorded_query_projection sound outputs
      simpa only [SourceFullOutputsV3.finishHard] using hp
  | bad A B C execution =>
    have hi:=SourceBadPairV3.bad_index sound execution
    have hp:=congrArg (List.map Prod.snd) hi
    simpa only [linear,List.map_map,Function.comp_def,CallbackPairingAuthor.indexFrom_project,SourceBadPairV3.complete] using hp

theorem selected_permutation
    (h : SelectedExec OrdExec mode T S c q out route r recorded chronological) :
    chronological.Perm recorded := by
  cases h with
  | empty => exact List.Perm.refl _
  | good A B C execution => exact List.Perm.refl _
  | hard execution => exact SourceFullOutputsV3.two_ledger_perm _
  | bad A B C execution => exact List.Perm.refl _

theorem selected_slots_realize
    (h : SelectedExec OrdExec mode T S c q out route r recorded chronological) :
    ∀ o∈recorded,SlotRealizes OrdExec mode o.2 := by
  cases h with
  | empty => simp
  | good A B C execution =>
    intro o ho
    obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ho
    exact SourceGoodPairV3.good_slots_realize execution s hs
  | hard execution =>
    cases execution with
    | run outputs => exact SourceFullOutputsV3.recorded_slots_realize outputs
  | bad A B C execution =>
    intro o ho
    obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ho
    exact SourceBadPairV3.bad_slots_realize execution s hs

theorem selected_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Hard2Overlap.Result) (route : PaidRoute) :
    ∃ r recorded chronological,SelectedExec OrdExec mode T S c q out route r recorded chronological := by
  cases route with
  | empty => exact ⟨_,_,_,SelectedExec.empty⟩
  | good A B C =>
    obtain ⟨r,slots,execution⟩:=SourceGoodPairV3.good_exists total T S A B C q
    exact ⟨_,_,_,SelectedExec.good A B C execution⟩
  | hard =>
    obtain ⟨r,cells,execution⟩:=SourceFullOutputsV3.outputs_exists total T S q 0 (actualOutputsMeter S T c q out).value
    exact ⟨_,_,_,SelectedExec.hard (SourceFullOutputsV3.HardPaidExec.run execution)⟩
  | bad A B C edge =>
    obtain ⟨r,debits,slots,execution⟩:=SourceBadPairV3.bad_exists total T S A B C edge q 0
    exact ⟨_,_,_,SelectedExec.bad A B C execution⟩

def finish (T S : Tree) (c : CherryBranching.Candidate) (out : Hard2Overlap.Result)
    (r : SourceExecution) : SourceExecution :=
  ⟨r.value,(paidOuterMeter T S c out).work+r.work⟩

inductive PaidExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Hard2Overlap.Result) :
    SourceExecution→List Occurrence→List Occurrence→Prop
  | run (execution : SelectedExec OrdExec mode T S c q out (paidOuterMeter T S c out).value r recorded chronological) :
      PaidExec OrdExec mode T S c q out (finish T S c out r) recorded chronological

theorem paid_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PaidExec OrdExec mode T S c q out r recorded chronological) :
    r=paidCaseCompleteSource (ordinarySpec mode base) (fun _ _ _=>0) T S c q out := by
  cases h with
  | run execution =>
    have hv:=selected_source_fields sound execution
    simp only [finish,paidCaseCompleteSource,hv]

theorem paid_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Hard2Overlap.Result) :
    ∃ r recorded chronological,PaidExec OrdExec mode T S c q out r recorded chronological := by
  obtain ⟨r,recorded,chronological,execution⟩:=selected_exists total T S c q out (paidOuterMeter T S c out).value
  exact ⟨_,_,_,PaidExec.run execution⟩
end SourcePaidCaseV3
