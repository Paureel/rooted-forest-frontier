import PendantMetadataV3

namespace SourceSelectedChildrenV3
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5SelectedLocalWork
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.FastOrdinary OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.CompleteSource OrdinaryDispatch.EarlyLocalWork
open SourceForestV3 SourceCouplingV2 SourceChildrenV2 SourceSelectedChildrenV2
open SourceDisjointV2 (ordinarySpec)
open SourcePendantValuesV3
open CallbackPairingAuthor (indexFrom)

variable {OrdExec : Tree→Tree→Nat→Option SourceForestV3.F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option SourceForestV3.F} {T S : Tree}

theorem one_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ChildrenExec OrdExec mode T q k [(pendantChildMeter S a b).value] r debits slots) :
    finishOne T S q a b r debits=oneSource (ordinarySpec mode base) (fun _ _ _=>0) T S q a b := by
  have hf:=children_source_fields sound h S
  simp only [finishOne,oneSource,hf]

theorem high_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ChildrenExec OrdExec mode T q k (branchesMeter S a b).value r debits slots) :
    finishHigh T S q a b r debits=highSource (ordinarySpec mode base) (fun _ _ _=>0) T S q a b := by
  have hf:=children_source_fields sound h S
  simp only [finishHigh,highSource,hf]

theorem one_actual_trace
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ChildrenExec OrdExec mode T q k [(pendantChildMeter S a b).value] r debits slots) :
    (finishOne T S q a b r debits).value=(childrenTrace (ordinarySpec mode base) T S q [pendantChild S a b]).value ∧
    slots.map (fun s=>(s.index,s.query))=
      indexFrom k (childrenTrace (ordinarySpec mode base) T S q [pendantChild S a b]).queries := by
  have ht:=children_actual_trace sound h S
  rw [pendantChild_value] at ht
  exact ht

theorem high_actual_trace
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ChildrenExec OrdExec mode T q k (branchesMeter S a b).value r debits slots) :
    (finishHigh T S q a b r debits).value=(childrenTrace (ordinarySpec mode base) T S q (branches S a b)).value ∧
    slots.map (fun s=>(s.index,s.query))=
      indexFrom k (childrenTrace (ordinarySpec mode base) T S q (branches S a b)).queries := by
  have ht:=children_actual_trace sound h S
  rw [SourcePendantValuesV3.branches_value] at ht
  exact ht

theorem actual_one_step
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ChildrenExec OrdExec (.cutoff q) (Oriented reverse T S).1 q k
      [(pendantChildMeter (Oriented reverse T S).2 c.a c.b).value] r debits slots)
    (proper : DepthOne.proper T S=true) (pretest : DepthOne.pretest01 T S=.rejected)
    (selected : early T S=.one reverse c) :
    (finishOne (Oriented reverse T S).1 (Oriented reverse T S).2 q c.a c.b r debits).value=
      (ordinaryStepTrace (fun b T S=>base T S b) q T S).value ∧
    slots.map (fun s=>(s.index,s.query))=
      indexFrom k (ordinaryStepTrace (fun b T S=>base T S b) q T S).queries := by
  have ht:=one_actual_trace sound h
  rw [cutoff_spec] at ht
  simpa only [ordinaryStepTrace,proper,↓reduceIte,pretest,selected] using ht

theorem actual_high_step
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ChildrenExec OrdExec (.cutoff q) (Oriented reverse T S).1 q k
      (branchesMeter (Oriented reverse T S).2 c.a c.b).value r debits slots)
    (proper : DepthOne.proper T S=true) (pretest : DepthOne.pretest01 T S=.rejected)
    (selected : early T S=.high reverse c) :
    (finishHigh (Oriented reverse T S).1 (Oriented reverse T S).2 q c.a c.b r debits).value=
      (ordinaryStepTrace (fun b T S=>base T S b) q T S).value ∧
    slots.map (fun s=>(s.index,s.query))=
      indexFrom k (ordinaryStepTrace (fun b T S=>base T S b) q T S).queries := by
  have ht:=high_actual_trace sound h
  rw [cutoff_spec] at ht
  simpa only [ordinaryStepTrace,proper,↓reduceIte,pretest,selected] using ht

end SourceSelectedChildrenV3
