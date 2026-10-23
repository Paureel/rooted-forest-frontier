import Rule5DispatchActualTraceV3

namespace SourceUnitCombineV3
open RMAF Universal233 SourceForestV3
open OrdinaryDispatch.OuterSource OrdinaryDispatch.Hard2Combine SourceLocalValuesV3 SourceChildMetadataV3

theorem unit_children_value (S : Tree) (a b : Nat) :
    (unitChildrenMeter S a b).value=[CherryBranching.singletonChild S a,CherryBranching.singletonChild S b] := by
  simp only [unitChildrenMeter,singletonChild_value]

theorem unit_calls_value (S T : Tree) (a b q : Nat) :
    (unitCallsMeter S T a b q).value=unitCalls S T a b q := by
  simp only [unitCallsMeter,unit_children_value,unitCalls]
end SourceUnitCombineV3
