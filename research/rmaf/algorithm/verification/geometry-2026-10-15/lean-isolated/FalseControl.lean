import Controls
namespace VertexGeometry.FalseControl
/-- Deliberately false when the nonlabel premise is dropped. -/
theorem false_avoidance_without_nonlabel :
    ([] : Vertex) ∉ RMAF.minimalVertices [0] (.leaf 0) := by decide
/-- Deliberately false heuristic: two removals always give three leaf regions. -/
theorem false_two_vertex_three_regions :
    (jointColors Controls.chainB Controls.chain [false] [true]).length = 3 := by decide
end VertexGeometry.FalseControl
