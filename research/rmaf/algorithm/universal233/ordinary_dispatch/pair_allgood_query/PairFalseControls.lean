import PairControls
open RMAF ForestState ForestGroups Universal233 OrdinaryDispatch.GoodPairDP OrdinaryDispatch.GoodPairDP.Controls
example : (AllGoodDP.run (localTarget (some target) (A++B)) (owned (OutputState.sourceForest (source badC) [A,B,C]) (A++B))).any (fun F=>decide (additionalCost (owned (OutputState.sourceForest (source badC) [A,B,C]) (A++B)) F=0))=true := by cbv
example : ((runPair depthAnswer target (source badC) A B C 4).calls.map Universal233.BothBad.Call.budget)=[2] := by cbv
example : (runPair depthAnswer target (source badC) A B C 3).answer.isSome=true := by cbv
example : (runPair depthAnswer target (source badC) A B C 2).answer.isSome=true := by cbv
