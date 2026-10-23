import CommonProjectionV3

namespace SourceChildMetadataV3
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence
open Universal233.Rule5SelectedLocalWork SourceLocalValuesV3

theorem contains_value (x : Nat) (xs : List Nat) : (meterContains x xs).value=xs.contains x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [meterContains,List.contains_cons]
    split <;> rename_i he
    · simp only [he,Bool.true_or]
    · simp only [he,Bool.false_or,ih]

theorem restrict_value (B : List Nat) (T : Tree) : (meterRestrict B T).value=restrict B T := by
  induction T with
  | leaf x => simp only [meterRestrict,restrict,contains_value]
  | node l r il ir =>
    simp only [meterRestrict,restrict,il,ir]
    rfl

theorem sourceForest_value (T : Tree) (P : List (List Nat)) :
    (sourceForestMeter T P).value=OutputState.sourceForest T P := by
  induction P with
  | nil => rfl
  | cons B P ih =>
    simp only [sourceForestMeter,OutputState.sourceForest,List.filterMap_cons,restrict_value]
    simp only [OutputState.sourceForest] at ih
    rw [ih]
    cases restrict B T <;> rfl

theorem makeChild_value (T : Tree) (P : List (List Nat)) (paid : Nat) :
    (makeChildMeter T P paid).value=CherryBranching.makeChild T P paid := by
  simp only [makeChildMeter,CherryBranching.makeChild,sourceForest_value,OutputState.sourceForest]

theorem singletonChild_value (T : Tree) (x : Nat) :
    (singletonChildMeter T x).value=CherryBranching.singletonChild T x := by
  simp only [singletonChildMeter,CherryBranching.singletonChild,singletonPartition_value,makeChild_value]

end SourceChildMetadataV3
