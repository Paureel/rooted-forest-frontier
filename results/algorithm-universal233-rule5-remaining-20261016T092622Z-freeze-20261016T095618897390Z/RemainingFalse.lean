import RemainingControls
namespace Universal233.Rule5RemainingLocalWork
open RMAF Rule5PrefixLocalWork
example : (permMeter [0,0] [0]).value=true := by decide
example : (setupMeter t2 t2 [0] [1] []).value.isSome=true := by decide
example : (markedMeter t2 [0] 1 7).value=some t2 := by decide
example : (rowsMeter bot 0 1 2).value=[] := by decide
example : (leafAddressMeter t2 1).value=some [false] := by decide
example : (setupMeter t2 t2 [0] [1] [false]).work=0 := by decide
end Universal233.Rule5RemainingLocalWork
