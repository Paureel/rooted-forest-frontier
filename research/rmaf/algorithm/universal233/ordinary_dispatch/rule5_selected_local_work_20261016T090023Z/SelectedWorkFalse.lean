import SelectedWorkControls
namespace Universal233.Rule5SelectedLocalWork
open RMAF CherryBranching
example : (sourceForestMeter t2 [[]]).work=0 := by decide
example : (sourceForestMeter t2 [[],[]]).work=(sourceForestMeter t2 [[]]).work := by decide
example : (pairChildMeter t2 0 1).value.paid=1 := by decide
example : (bestLengthMeter allCheck [[[0]],[]]).value=some [[0]] := by decide
example : (runChildrenMeter noOrdinary forestFee agreementFee t2 t2 1 [singletonChild t2 0,singletonChild t2 0]).calls.length=1 := by decide
end Universal233.Rule5SelectedLocalWork
