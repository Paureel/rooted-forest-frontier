import HandlerControls
open Universal233.Rule5OrdinaryDispatch Universal233.Rule5OrdinaryDispatch.Controls
open Universal233.Rule5Local.Pre
-- Deliberately omit one literal paid-two branch: must fail.
example : (sourceJobs twoT twoS 6).length=4 := by decide
