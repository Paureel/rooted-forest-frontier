import Composition
namespace VertexGeometry.Controls
open RMAF

/-- Three disjoint source parents use the three pairs of incident directions.
Their target spans share one vertex and no edge. -/
def tripod : Tree := .node (.node (.leaf 4) (.leaf 5))
  (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
def tripodA : List Nat := [0,2]
def tripodB : List Nat := [3,4]
def tripodC : List Nat := [5,1]
def commonVertices : List Vertex := (minimalVertices tripodA tripod).filter
  (fun v => (minimalVertices tripodB tripod).contains v &&
    (minimalVertices tripodC tripod).contains v)

theorem clique_common_vertex_no_common_edge : commonVertices = [[true]] := by decide

theorem tripod_A_two_regions : (regions tripodA tripod [true]).length = 2 := by decide
theorem tripod_B_two_regions : (regions tripodB tripod [true]).length = 2 := by decide
theorem tripod_C_two_regions : (regions tripodC tripod [true]).length = 2 := by decide

/-- Chain v=[false], w=[true]. The root is the leafless middle component after
removing v,w. End-parent target spans are disjoint and B has two leaf regions. -/
def chain : Tree := .node
  (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
  (.node (.node (.leaf 3) (.leaf 4)) (.leaf 5))
def chainA : List Nat := [1,2]
def chainB : List Nat := [0,3]
def chainC : List Nat := [4,5]

theorem chain_endpoints_disjoint :
    disjointVertices (minimalVertices chainA chain) (minimalVertices chainC chain) = true := by decide

theorem chain_intersections :
    [false] ∈ minimalVertices chainA chain ∧ [false] ∈ minimalVertices chainB chain ∧
    [true] ∈ minimalVertices chainB chain ∧ [true] ∈ minimalVertices chainC chain := by decide

theorem chain_two_joint_regions : (jointColors chainB chain [false] [true]).length = 2 := by decide

theorem root_two_regions : (regions [0,3] chain []).length = 2 := by decide

theorem singleton_requires_nonlabel_hypothesis :
    ([] : Vertex) ∈ minimalVertices [0] (.leaf 0) := by decide

/-- Wrongly adding independent same-parent cut-list lengths double-counts.
The correct cut union contains one original edge, not two paid edges. -/
def reusedCut : List SourceEdge := [(1,[false])]
theorem same_parent_union_not_additive :
    (reusedCut ++ reusedCut).eraseDups.length = 1 ∧ reusedCut.length + reusedCut.length = 2 := by decide

end VertexGeometry.Controls
