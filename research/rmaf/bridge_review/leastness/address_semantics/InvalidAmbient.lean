import TreeAddresses
open RMAF LeastEmbedding
example : [false, false] ∈ vertices (.node (.leaf 5) (.leaf 5)) := by decide
