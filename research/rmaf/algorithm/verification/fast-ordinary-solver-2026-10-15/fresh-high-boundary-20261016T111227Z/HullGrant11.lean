-- Three generic hull primitives, isolated types in GraphTypes07.
import NativeAuditCore
run_cmd StageAudit.audit #[`VertexGeometry.minimalVertices_correct,
  `VertexGeometry.executable_span_monotone, `VertexGeometry.hull_convex,
  `Universal233.CoreGraph.subtree_append] "hull-grant-v1"
