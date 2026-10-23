import RMAF
import GraphRegion

namespace ExecutableBridge.Controls
open RMAF BridgeReview

def quartet : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def crossing : List Vertex := [[],[false],[false,false],[true],[true,false]]
def deletedPath : List Vertex := [[],[false,false],[true],[true,false]]

theorem crossing_exact : minimalVertices [0,2] quartet = crossing := by decide
theorem singleton_exact : minimalVertices [1] quartet = [[false,true]] := by decide
theorem siblings_exact : minimalVertices [0,1] quartet = [[false],[false,false],[false,true]] := by decide
theorem empty_exact : minimalVertices [] quartet = [] := by decide
theorem absent_exact : minimalVertices [9] quartet = [] := by decide
theorem path_deletion_rejected : minimalVertices [0,2] quartet ≠ deletedPath := by decide

theorem deleted_path_disconnected :
    ¬ Walk (fun v => v ∈ deletedPath) [] [false,false] := by
  intro w
  have h := walk_ancestor_between w [false] (by decide) (by decide)
  have hn : [false] ∉ deletedPath := by decide
  exact hn h

#print axioms crossing_exact
#print axioms singleton_exact
#print axioms siblings_exact
#print axioms empty_exact
#print axioms absent_exact
#print axioms path_deletion_rejected
#print axioms deleted_path_disconnected
end ExecutableBridge.Controls
