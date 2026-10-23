import ModeBindingsV3

namespace SourceRule4V3
open RMAF Universal233 WholeSourceWork CoreWork
open SourceForestV3 SourceCouplingV2
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.CompleteSource OrdinaryDispatch.EarlyLocalWork

variable {OrdExec : Tree→Tree→Nat→Option SourceForestV3.F→Prop}
  {base : Tree→Tree→Nat→Option SourceForestV3.F} {T S : Tree}

theorem rule4_complete_forward_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=OrdinaryDispatch.FastOrdinary.solve b T S)
    (h : Rule4Exec OrdExec (.cutoff q) s q out cells) :
    out=completeBranchSource (fun _ _ _=>0) q T S (.rule4Forward s) := by
  have hf:=rule4_source_fields (base:=fun T S b=>OrdinaryDispatch.FastOrdinary.solve b T S) sound h
  rw [cutoff_spec] at hf
  exact hf

theorem rule4_complete_reverse_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=OrdinaryDispatch.FastOrdinary.solve b T S)
    (h : Rule4Exec OrdExec (.cutoff q) s q out cells) :
    out=completeBranchSource (fun _ _ _=>0) q T S (.rule4Reverse s) := by
  have hf:=rule4_source_fields (base:=fun T S b=>OrdinaryDispatch.FastOrdinary.solve b T S) sound h
  rw [cutoff_spec] at hf
  exact hf

theorem rule4_forward_local_credit
    (sound : ∀ T S b a,OrdExec T S b a→a=OrdinaryDispatch.FastOrdinary.solve b T S)
    (h : Rule4Exec OrdExec (.cutoff q) s q out cells)
    (selected : (meterFront q T S).value=.selected (.rule4Forward s)) :
    out.work≤completeLocalDebit T S q := by
  have hf:=rule4_complete_forward_fields sound h
  simp only [completeLocalDebit,ordinaryCompleteStepSource,selected]
  rw [←hf]
  exact Nat.le_add_left _ _

theorem actual_rule4_forward_step
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Rule4Exec OrdExec (.cutoff q) s q out cells)
    (proper : DepthOne.proper T S=true)
    (pretest : DepthOne.pretest01 T S=.rejected)
    (selected : early T S=.rule4Forward s) :
    out.value=(ordinaryStepTrace (fun b T S=>base T S b) q T S).value ∧
    (recorded cells).map (fun ls=>ls.2.query)=
      (ordinaryStepTrace (fun b T S=>base T S b) q T S).queries := by
  have ht:=rule4_actual_trace sound h
  rw [cutoff_spec] at ht
  simpa only [ordinaryStepTrace,proper,↓reduceIte,pretest,selected] using ht

theorem actual_rule4_reverse_step
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Rule4Exec OrdExec (.cutoff q) s q out cells)
    (proper : DepthOne.proper T S=true)
    (pretest : DepthOne.pretest01 T S=.rejected)
    (selected : early T S=.rule4Reverse s) :
    out.value=(ordinaryStepTrace (fun b T S=>base T S b) q T S).value ∧
    (recorded cells).map (fun ls=>ls.2.query)=
      (ordinaryStepTrace (fun b T S=>base T S b) q T S).queries := by
  have ht:=rule4_actual_trace sound h
  rw [cutoff_spec] at ht
  simpa only [ordinaryStepTrace,proper,↓reduceIte,pretest,selected] using ht

end SourceRule4V3
