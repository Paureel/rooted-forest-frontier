import NumericInterface
open OrdinaryDispatch.GlobalNumeric
example : semanticWidth 3 2 10 = 31 := by decide +kernel
example : representedCapacityEnvelope 3 2 10 = 56 := by decide +kernel
example : 10 > (RMAF.leaves (RMAF.Tree.leaf 0)).length := by decide +kernel
