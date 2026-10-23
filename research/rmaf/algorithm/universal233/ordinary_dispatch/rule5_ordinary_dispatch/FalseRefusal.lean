import HandlerControls
open Universal233.Rule5OrdinaryDispatch Universal233.Rule5OrdinaryDispatch.Controls
open Universal233.Rule5Local.Pre
-- Admitted zero budget is answered infeasible, not builder/selector refusal.
example : dispatch emptyCallback sixT sixS 0 1 0=.selectorRefused := by decide
