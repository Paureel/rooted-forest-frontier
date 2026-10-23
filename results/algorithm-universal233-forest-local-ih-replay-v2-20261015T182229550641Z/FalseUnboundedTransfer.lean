import TransferControls
open RMAF GenericForest GenericForest.Controls GenericForest.LocalIH.Controls
theorem false_above_bound_transfer :
    solve tooSmall (some (.node (four 0) (cross 4))) [four 0,four 4] 2 =
      some [[0,1,2,3],[4],[5],[6,7]] := by cbv
