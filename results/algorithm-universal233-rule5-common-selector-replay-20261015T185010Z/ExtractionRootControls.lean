import ExtractionControls
namespace Universal233.Case322Extraction.Controls
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching
open VertexGeometry
open Universal233.Rule5Local Universal233.Rule5Case322 Universal233.Case322Extraction

def rootT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.node (.leaf 5) (.node (.leaf 8) (.leaf 9))))
def rootS : Tree := .node (.node (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 5) (.leaf 9)))) (.leaf 2)) (.leaf 1)
theorem root_original_X_pendant : (incident rootT [5,8,9]).length = 1 := by decide
theorem root_cside_one : cSideEdges rootT 1 2 = [[true,true]] := by decide
theorem root_bside_empty : bSideWithoutA rootT 0 1 2 = [] := by decide
theorem root_lca_empty : lca [false,true] [true,false] = [] := by rfl
theorem root_guard_rejects :
 (rawPlan rootT rootS 0 1 2 [false,false] [true] [false,true] [true,false]).all (currentGuard rootT rootS) = false := by decide
end Universal233.Case322Extraction.Controls
