import Controls
open RMAF FreshClade
-- Deliberately false universal-extension instance: this file must fail.
example : agreement balanced balanced (splitForest [0,2] [[0,1,2,3]]) = true := by decide
