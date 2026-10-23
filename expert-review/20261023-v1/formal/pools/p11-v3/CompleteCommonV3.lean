import ChildMetadataV3
import CompleteOrdinaryStep

namespace SourceCommonV3
open RMAF Universal233 WholeSourceWork
open OrdinaryDispatch.CompleteSource OrdinaryDispatch.EarlyLocalWork
open SourceForestV3

variable {OrdExec : Tree→Tree→Nat→Option SourceForestV3.F→Prop} {T S : Tree}

theorem common_complete_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=OrdinaryDispatch.FastOrdinary.solve b T S)
    (h : CommonExec OrdExec q T S reverse c k out slots) :
    out=completeBranchSource (fun _ _ _=>0) q T S (.common reverse c) := by
  simpa only [completeBranchSource] using
    (common_source_fields (base:=fun T S b=>OrdinaryDispatch.FastOrdinary.solve b T S) sound h)

theorem common_local_credit
    (sound : ∀ T S b a,OrdExec T S b a→a=OrdinaryDispatch.FastOrdinary.solve b T S)
    (h : CommonExec OrdExec q T S reverse c k out slots)
    (selected : (meterFront q T S).value=.selected (.common reverse c)) :
    out.work≤completeLocalDebit T S q := by
  have hf:=common_complete_fields sound h
  simp only [completeLocalDebit,ordinaryCompleteStepSource,selected]
  rw [←hf]
  exact Nat.le_add_left _ _

end SourceCommonV3
