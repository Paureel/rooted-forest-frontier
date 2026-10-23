import TreeAddresses
open RMAF LeastEmbedding
example : terminals [5] (.node (.leaf 5) (.leaf 5)) = [[false]] := by decide
