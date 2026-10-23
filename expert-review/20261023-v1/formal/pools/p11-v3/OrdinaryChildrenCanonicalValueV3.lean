import GroupedRetainedOutputV3

namespace SourceSelectedChildrenV3
open RMAF Universal233 SourceForestV3 SourceChildrenV2 SourceCouplingV2
open Universal233.Rule5SelectedLocalWork
open OrdinaryDispatch.FullSourceWork SourcePendantValuesV3
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem one_parent_raw
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ChildrenExec OrdExec mode T q k [(pendantChildMeter S a b).value] r debits slots) :
    (SourceSelectedChildrenV2.finishOne T S q a b r debits).value=
      OrdinaryDispatch.runChildren (ordinarySpec mode base) T S q [CherryBranching.pendantChild S a b] := by
  have hv:=children_parent_raw sound h S
  rw [pendantChild_value] at hv
  exact hv

theorem high_parent_raw
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ChildrenExec OrdExec mode T q k (branchesMeter S a b).value r debits slots) :
    (SourceSelectedChildrenV2.finishHigh T S q a b r debits).value=
      OrdinaryDispatch.runChildren (ordinarySpec mode base) T S q (CherryBranching.branches S a b) := by
  have hv:=children_parent_raw sound h S
  rw [SourcePendantValuesV3.branches_value] at hv
  exact hv
end SourceSelectedChildrenV3
