import Pretest

namespace Universal233.DepthOne.Controls
open RMAF CoreGraph

def crossed : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))

theorem known_zero : pretest01 RMAF.Controls.leftTree RMAF.Controls.leftTree = .found none := by decide
theorem known_one : pretest01 RMAF.Controls.leftTree RMAF.Controls.rightTree = .found (some [false,true,true]) := by decide
theorem original_one_witness : forest RMAF.Controls.rightTree (some [false,true,true]) = [[2],[0,1,3]] ∧
    agreement RMAF.Controls.leftTree RMAF.Controls.rightTree [[2],[0,1,3]] = true := by decide
theorem known_two_rejects : pretest01 RMAF.Controls.leftTree crossed = .rejected := by decide
set_option maxRecDepth 10000 in
theorem known_two_minimum : (solve 4 RMAF.Controls.leftTree crossed).map (fun a => (blocks a).length - 1) = some 2 := by decide
theorem singleton_zero : pretest01 (.leaf 71) (.leaf 71) = .found none := by decide
theorem absent_label_refused : pretest01 (.leaf 71) (.leaf 72) = .refused := by decide
theorem repeated_label_refused : pretest01 (.node (.leaf 7) (.leaf 7)) (.node (.leaf 7) (.leaf 7)) = .refused := by decide
theorem empty_partition_rejected : agreement (.leaf 7) (.leaf 7) [] = false := by decide
theorem whole_B_false_one_cut :
    ((edges crossed).map (fun p => forest crossed (some p))).all
      (fun F => !(agreement RMAF.Controls.leftTree crossed F)) = true := by decide
theorem root_excluded : ([] : Vertex) ∉ edges crossed := by decide
theorem original_suppressed_parent :
    [false,true,true] ∈ edges RMAF.Controls.rightTree ∧
    ([false,true,true] : Vertex).dropLast = [false,true] ∧
    subtree RMAF.Controls.rightTree [false,true] = some (.node (.leaf 1) (.leaf 2)) := by decide

end Universal233.DepthOne.Controls
