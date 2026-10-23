import Hard2ChoiceValueV3

namespace SourceGoodPairV3
open RMAF Universal233 WholeSourceWork CoreWork SourceForestV3
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.GoodPairDP
open Universal233.Rule5SelectedLocalWork SourceChildMetadataV3
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)

-- Unfold the pure append body; the accidentally exposed theorem is not used.
theorem append_value (A B : List Nat) : (appendLabelsMeter A B).value=A++B := rfl

theorem good_source_raw_value (actual : GenericForest.FrontierWork.Ordinary)
    (W : GenericForest.FrontierWork.OrdinaryWork) (T S : Tree) (A B C : List Nat) (q : Nat) :
    (goodPairSource actual W T S A B C q).value=runPair actual T S A B C q := by
  simp only [goodPairSource,goodPairLocalSource,runPair,sourceForest_value,append_value,
    localTargetMeter_value,ownedMeter_value,AllGoodDP.LocalWork.meterRun_value,
    additionalCostMeter_value,checkedMeter_value]
  by_cases enough:2≤q
  · simp only [enough,↓reduceIte]
    cases he:AllGoodDP.run (ForestGroups.localTarget (some T) (A++B))
      (ForestGroups.owned (OutputState.sourceForest S [A,B,C]) (A++B)) with
    | none => rfl
    | some H =>
      dsimp only
      by_cases paid:ForestState.additionalCost (ForestGroups.owned (OutputState.sourceForest S [A,B,C]) (A++B)) H≤q-2
      · simp only [paid,↓reduceIte]
      · simp only [paid,↓reduceIte]
  · simp only [enough,↓reduceIte]

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree} {A B C : List Nat}
theorem good_raw_execution
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : GoodExec OrdExec mode T S A B C q r slots) :
    r.value=runPair (ordinarySpec mode base) T S A B C q := by
  rw [good_source_fields sound h,good_source_raw_value]
end SourceGoodPairV3
