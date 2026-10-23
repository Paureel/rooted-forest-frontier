import CompleteRule4V3

namespace SourcePendantValuesV3
open RMAF Universal233 Universal233.HardParent
open Universal233.Rule5PrefixLocalWork Universal233.Rule5PendantLocalWork
open Universal233.Rule5SelectedLocalWork SourceLocalValuesV3 SourceChildMetadataV3

theorem flatten_value (bs : List (List Nat)) : (flattenMeter bs).value=bs.flatten := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [flattenMeter,List.flatten_cons,ih]

theorem payload_value (T : Tree) (a b : Nat) : (pendantPayloadMeter T a b).value=
    ((CherryBranching.cuts T a b).map (HardParent.subtreeLabels T)).flatten := by
  simp only [pendantPayloadMeter,CherryBranching.cuts,cuts_value,SourceLocalValuesV3.blocks_value,flatten_value]

theorem coreFilter_value (T : Tree) (a b : Nat) (xs : List Nat) :
    (coreFilterMeter T a b xs).value=xs.filter
      (fun x=>!((CherryBranching.cuts T a b).map (HardParent.subtreeLabels T)).flatten.contains x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [coreFilterMeter,List.filter_cons,payload_value,prefixContains_value,ih]

theorem core_value (T : Tree) (a b : Nat) : (coreMeter T a b).value=CherryBranching.coreLabels T a b := by
  simp only [coreMeter,CherryBranching.coreLabels,prefixLeaves_value,coreFilter_value]

theorem partition_value (T : Tree) (a b : Nat) :
    (partitionMeter T a b).value=CherryBranching.pendantPartition T a b := by
  simp only [partitionMeter,CherryBranching.pendantPartition,CherryBranching.cuts,
    cuts_value,SourceLocalValuesV3.blocks_value,core_value]

theorem pendantChild_value (T : Tree) (a b : Nat) :
    (pendantChildMeter T a b).value=CherryBranching.pendantChild T a b := by
  simp only [pendantChildMeter,CherryBranching.pendantChild,partition_value,makeChild_value,
    CherryBranching.cuts,cuts_value]

theorem branches_value (T : Tree) (a b : Nat) :
    (OrdinaryDispatch.FullSourceWork.branchesMeter T a b).value=CherryBranching.branches T a b := by
  simp only [OrdinaryDispatch.FullSourceWork.branchesMeter,CherryBranching.branches,
    singletonChild_value,pendantChild_value]

end SourcePendantValuesV3
