import GeometryFreshControls
namespace GeometryFreshNegative
open RMAF VertexGeometry
-- Pre-candidate below-root false expectation: the original root is absent.
theorem false_original_root :
  ([] : VertexGeometry.Vertex) ∈ minimalVertices [1,2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) := by decide +kernel
-- Pre-candidate leafless middle false expectation: it contributes no third color.
theorem false_leafless_third_color :
  (jointColors [0,1] (.node (.node (.leaf 0) (.leaf 7)) (.node (.leaf 8) (.node (.leaf 9) (.node (.leaf 1) (.leaf 10))))) [] [true,true,true]).length = 3 := by decide +kernel
end GeometryFreshNegative
