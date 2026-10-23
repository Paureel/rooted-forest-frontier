import DegreeCounting

namespace DegreeTwo.LocalControls
open RMAF BridgeReview DegreeTwoGraph

def rootTree : Tree := .node (.leaf 0) (.leaf 1)
def pathTree : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)

theorem root_degree : actualDegree rootTree [0,1] [] = 2 := by decide
theorem path_degree : actualDegree pathTree [0,2] [false] = 2 := by decide
theorem degree_three : actualDegree pathTree [0,1,2] [false] = 3 := by decide
theorem singleton_degree : actualDegree pathTree [0] [false,false] = 0 := by decide
theorem empty_degree : actualDegree pathTree [] [] = 0 := by decide
theorem absent_degree : actualDegree pathTree [99] [] = 0 := by decide

theorem root_blocks : belowBlock rootTree [false] [0,1] = [0] ∧
    outsideBlock rootTree [false] [0,1] = [1] := by decide
theorem path_blocks : belowBlock pathTree [false,false] [0,2] = [0] ∧
    outsideBlock pathTree [false,false] [0,2] = [2] := by decide

theorem path_exact_unsuppressed : minimalVertices [0,2] pathTree =
    [[],[false],[false,false],[true]] := by decide

theorem root_general_split : ∃ b0 b1 : List Nat,
    b0 ≠ [] ∧ b1 ≠ [] ∧ b0.Nodup ∧ b1.Nodup ∧
    (b0 ++ b1).Perm [0,1] ∧ (∀ x, x ∈ b0 → x ∉ b1) ∧
    EmbSub rootTree b0 [0,1] ∧ EmbSub rootTree b1 [0,1] ∧
    disjointVertices (minimalVertices b0 rootTree) (minimalVertices b1 rootTree) = true ∧
    [] ∉ minimalVertices b0 rootTree ∧ [] ∉ minimalVertices b1 rootTree := by
  obtain ⟨hv,hd⟩ := (actualDegree_two_iff rootTree [0,1] []).mp root_degree
  exact actual_one_tree_split rootTree [0,1] [] (by decide) (by decide) hv hd

theorem path_general_split : ∃ b0 b1 : List Nat,
    b0 ≠ [] ∧ b1 ≠ [] ∧ b0.Nodup ∧ b1.Nodup ∧
    (b0 ++ b1).Perm [0,2] ∧ (∀ x, x ∈ b0 → x ∉ b1) ∧
    EmbSub pathTree b0 [0,2] ∧ EmbSub pathTree b1 [0,2] ∧
    disjointVertices (minimalVertices b0 pathTree) (minimalVertices b1 pathTree) = true ∧
    [false] ∉ minimalVertices b0 pathTree ∧ [false] ∉ minimalVertices b1 pathTree := by
  obtain ⟨hv,hd⟩ := (actualDegree_two_iff pathTree [0,2] [false]).mp path_degree
  exact actual_one_tree_split pathTree [0,2] [false] (by decide) (by decide) hv hd

theorem degree_three_not_exact_two :
    ¬ ExactTwo (fun w => w ∈ minimalVertices [0,1,2] pathTree) [false] := by
  intro h
  have he := (actualDegree_two_iff pathTree [0,1,2] [false]).mpr ⟨by decide,h⟩
  rw [degree_three] at he
  contradiction

end DegreeTwo.LocalControls
