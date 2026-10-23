import Controls
open Universal233.Integration Universal233.Integration.Controls RMAF

-- Corrupted twin: source block coverage alone does not imply hull disjointness.
example : RMAF.pairwiseEmbeddings
    (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,2],[1,3]] = true := by decide

-- Corrupted twin: both old terminals collapse to the same quotient vertex.
example : cherryProjection [] [false] ≠ cherryProjection [] [true] := by decide

-- Corrupted twin: after suppression, an executable edge can expand to two original edges.
example : (erasureEmbedding expandedErasure [false]).length = 1 := by decide
