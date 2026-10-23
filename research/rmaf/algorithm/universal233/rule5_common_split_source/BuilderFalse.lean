import BuilderControls
open OrdinaryCommonSplit.Source OrdinaryCommonSplit.GraphControls
example : (buildSetup rootT rootS X Y [false,false]).map (fun d=>d.rho)=some 0 := by decide
example : (buildSetup rootT rootS X Y []).isSome=true := by decide
