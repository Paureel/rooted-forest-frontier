import FullOutputsOccurrenceV3

namespace SourceSelectedChildrenV3
open RMAF Universal233 Universal233.Rule5SelectedLocalWork
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.FastOrdinary
open OrdinaryDispatch.CompleteSource OrdinaryDispatch.EarlyLocalWork
open SourceForestV3 SourceSelectedChildrenV2

variable {OrdExec : Tree→Tree→Nat→Option SourceForestV3.F→Prop} {T S : Tree}

theorem one_complete_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=OrdinaryDispatch.FastOrdinary.solve b T S)
    (h : ChildrenExec OrdExec (.cutoff q) (Oriented reverse T S).1 q k
      [(pendantChildMeter (Oriented reverse T S).2 c.a c.b).value] r debits slots) :
    finishOne (Oriented reverse T S).1 (Oriented reverse T S).2 q c.a c.b r debits=
      completeBranchSource (fun _ _ _=>0) q T S (.one reverse c) := by
  have hf:=one_source_fields (base:=fun T S b=>OrdinaryDispatch.FastOrdinary.solve b T S) sound h
  rw [cutoff_spec] at hf
  exact hf

theorem high_complete_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=OrdinaryDispatch.FastOrdinary.solve b T S)
    (h : ChildrenExec OrdExec (.cutoff q) (Oriented reverse T S).1 q k
      (branchesMeter (Oriented reverse T S).2 c.a c.b).value r debits slots) :
    finishHigh (Oriented reverse T S).1 (Oriented reverse T S).2 q c.a c.b r debits=
      completeBranchSource (fun _ _ _=>0) q T S (.high reverse c) := by
  have hf:=high_source_fields (base:=fun T S b=>OrdinaryDispatch.FastOrdinary.solve b T S) sound h
  rw [cutoff_spec] at hf
  exact hf

theorem one_local_credit
    (sound : ∀ T S b a,OrdExec T S b a→a=OrdinaryDispatch.FastOrdinary.solve b T S)
    (h : ChildrenExec OrdExec (.cutoff q) (Oriented reverse T S).1 q k
      [(pendantChildMeter (Oriented reverse T S).2 c.a c.b).value] r debits slots)
    (selected : (meterFront q T S).value=.selected (.one reverse c)) :
    (finishOne (Oriented reverse T S).1 (Oriented reverse T S).2 q c.a c.b r debits).work≤completeLocalDebit T S q := by
  have hf:=one_complete_fields sound h
  simp only [completeLocalDebit,ordinaryCompleteStepSource,selected]
  rw [←hf]
  exact Nat.le_add_left _ _

theorem high_local_credit
    (sound : ∀ T S b a,OrdExec T S b a→a=OrdinaryDispatch.FastOrdinary.solve b T S)
    (h : ChildrenExec OrdExec (.cutoff q) (Oriented reverse T S).1 q k
      (branchesMeter (Oriented reverse T S).2 c.a c.b).value r debits slots)
    (selected : (meterFront q T S).value=.selected (.high reverse c)) :
    (finishHigh (Oriented reverse T S).1 (Oriented reverse T S).2 q c.a c.b r debits).work≤completeLocalDebit T S q := by
  have hf:=high_complete_fields sound h
  simp only [completeLocalDebit,ordinaryCompleteStepSource,selected]
  rw [←hf]
  exact Nat.le_add_left _ _

end SourceSelectedChildrenV3
