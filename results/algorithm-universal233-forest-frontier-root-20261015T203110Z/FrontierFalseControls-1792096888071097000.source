import FrontierControls
namespace GenericForest.FrontierControls
open RMAF ForestState Universal233 Universal233.PaidQueries GenericForest.FrontierWork
example : frontier noOrd (some target3) [source3] 2=[((target3,source3),1)] := by
 rw [singleton_literal]; decide
example : (frontier noOrd (some target3) [target3] 2).isEmpty=false := by
 rw [solved_literal]; decide
example : (frontier noOrd (some target3) [.leaf 0,.leaf 0] 2).isEmpty=false := by
 rw [malformed_literal]; decide
example : queryWork (fun _ _ _=>3) (frontier noOrd (some target3) [source3] 2)=0 := by
 rw [ordinary_work_once]; decide
example : geometric 3≤1 := by rw [actual_geometric_three]; decide
end GenericForest.FrontierControls
