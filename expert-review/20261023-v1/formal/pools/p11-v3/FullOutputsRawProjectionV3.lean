import ParentChildrenRawProjectionV3

namespace SourceFullOutputsV3
open RMAF Universal233 WholeSourceWork CoreWork SourceForestV3
open OrdinaryDispatch.Hard2SourceWork SourceHard2ValuesV3 SourceChildMetadataV3
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)

-- Return/call-list equality only. Actual source evaluation remains tail first.
theorem outputs_raw_value (actual : GenericForest.FrontierWork.Ordinary)
    (W : GenericForest.FrontierWork.OrdinaryWork) (T S : Tree) (q : Nat) (os : List CoreProgram.Output) :
    (fullOutputsSource actual W T S q os).value=
      BothBad.execute (GenericForest.solve actual) T S q (BothBad.entries q .full os) := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    simp only [BothBad.entries,BothBad.Mode.extra,Nat.add_zero,Nat.sub_zero] at ih
    simp only [fullOutputsSource,BothBad.entries,List.filterMap_cons,BothBad.Mode.extra,Nat.add_zero,Nat.sub_zero]
    by_cases paid:o.sourceCuts.length≤q
    · simp only [paid,↓reduceIte,BothBad.execute,BothBad.dispatch,checkedMeter_value,
        choose_value,sourceForest_value,ih]
      rfl
    · simpa only [paid,↓reduceIte] using ih

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem outputs_raw_execution
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : OutputsExec OrdExec mode T S q i os r cells) :
    r.value=Hard2PaidLocal.runOutputs (ordinarySpec mode base) T S q os := by
  rw [outputs_source_fields sound h,outputs_raw_value]
  rfl

theorem hard_paid_raw_execution
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : HardPaidExec OrdExec mode T S q c out r cells) :
    r.value=Hard2PaidLocal.runHardPaid (ordinarySpec mode base) T S q c out := by
  cases h with
  | run execution =>
    have hv:=outputs_raw_execution sound execution
    simpa only [finishHard,actualOutputsMeter_value,Hard2PaidLocal.runHardPaid] using hv
end SourceFullOutputsV3
