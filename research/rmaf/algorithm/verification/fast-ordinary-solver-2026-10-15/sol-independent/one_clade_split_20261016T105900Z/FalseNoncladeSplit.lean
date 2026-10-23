import CladeControls
open RMAF IndependentOneExchange ContactedClade
example : agreement balanced balanced (splitForest [0,2] [[0,1,2,3]])=true := by decide
