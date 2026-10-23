import Controls
open TripleDP.CostRoute
-- Deliberately false M1. The only semantic change from CleanTwin is 2 -> 1.
example : cherryClosed.blockCount = 1 := by decide
-- Deliberately false M2. Adjacent equal-color blocks must remain distinct.
example : adjacentSameColor.blockCount = 1 := by decide
