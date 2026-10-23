import TraceControls
open RMAF Universal233.Rule5ActualTrace Universal233.Rule5ActualTrace.Controls
open Universal233.Rule5Local.Pre
set_option maxRecDepth 24000
set_option maxHeartbeats 4000000
-- Actual common direct calls must not be replaced with forest jobs.
example : kind (dispatchTrace fail commonT commonS 0 1 4).calls=1 := by decide +kernel
-- Failed direct callbacks are still two occurrences.
example : (queries fail (dispatchTrace fail commonT commonS 0 1 4).calls).length=1 := by decide +kernel
-- Refund the complete separator payment: must reject.
example : (queries fail (dispatchTrace fail commonT commonS 0 1 4).calls).map Prod.snd=[4,4] := by decide +kernel
-- Fabricated3/4 labels must not replace the actual original cut list.
example : outerPayments (dispatchTrace fail sixT sixS 0 1 4).calls=[3,4,4,4] := by decide +kernel
