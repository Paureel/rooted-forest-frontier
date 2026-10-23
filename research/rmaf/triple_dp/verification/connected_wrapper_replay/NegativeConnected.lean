import ConnectedRegions
open TripleDP

-- Deliberately false: the retained LCA-closed region omits this path vertex.
example : gappedRegion [false] := by
  change ([false] : Address) = [] ∨ ([false] : Address) = [false, false]
  decide
