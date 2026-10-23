import AssemblyControls
open RMAF Universal233.Assembly Universal233.Assembly.Controls
example : parentTag [0] [1] 0 = parentTag [0] [1] 1 := by decide
example : (Universal233.CoreProgram.generate cliqueS (requestedColor cliqueT ca cb .keep (.at v) (.at v)) 0).outputs.isEmpty = false := by decide
example : literalCosts diagS diagT da db .keep (.both v w) .keep 5 = [4] := by decide
example : refinesBool [[0,1]] [[0],[1]] = true := by decide
