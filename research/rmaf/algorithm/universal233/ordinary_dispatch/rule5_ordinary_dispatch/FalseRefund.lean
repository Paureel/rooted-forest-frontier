import HandlerControls
open Universal233.Rule5OrdinaryDispatch Universal233.Rule5OrdinaryDispatch.Controls
open Universal233.Rule5Local.Pre
-- Deliberately refund every paid original cut: must fail.
example : ((sourceJobs firstT firstS 6).map ForestJob.residual)=[6,6] := by decide
