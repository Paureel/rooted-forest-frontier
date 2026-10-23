import ForestSelection
namespace GenericForest.Controls
open RMAF ForestState
theorem actual_crossed_solver : solve table (some (four 0)) ss 1 = some [[0],[2],[1,3]] ∧
    solve table (some (four 0)) ss 0 = none := by cbv
theorem actual_disjoint_solver :
    solve table (some (.node (four 0) (cross 4))) [four 0,four 4] 2 =
      some [[0,1,2,3],[4],[5],[6,7]] ∧
    solve table (some (.node (four 0) (cross 4))) [four 0,four 4] 1 = none := by cbv
theorem actual_boundaries : solve table none [] 0 = some [] ∧
    solve table (some (.leaf 7)) [.leaf 7] 0 = some [[7]] ∧
    solve table (some (.leaf 7)) [] 3 = none := by cbv
end GenericForest.Controls
