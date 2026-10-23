import Hard2SourceControls
namespace OrdinaryDispatch.Hard2SourceWork.Controls
open RMAF ForestState Universal233 GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration

theorem corrupt_edge_as_vertex :
 (pairChooseMeter cross [0,1] [2,3]).value=some (.vertex []) := by cbv

theorem corrupt_disjoint_as_clique :
 (runHard2Meter Hard2Dispatcher.Controls.T Hard2Dispatcher.Controls.S Hard2Dispatcher.Controls.c).value=some (.clique []) := by cbv

theorem corrupt_duplicate_query_drop :
 (forestQueries refused (Hard2PaidLocal.runOutputs refused Hard2Dispatcher.Controls.T Hard2Dispatcher.Controls.S 0 [output,output]).calls).length=1 := by
 rw [full_outputs_duplicate_queries]
 decide +kernel
end OrdinaryDispatch.Hard2SourceWork.Controls
