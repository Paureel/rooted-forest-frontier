import HandlerControls
open Universal233.Rule5OrdinaryDispatch Universal233.Rule5OrdinaryDispatch.Controls
open Universal233.Rule5Local.Pre Universal233.Rule5FinalClassification
-- Wrong saved original branch: must fail.
example : tag (selectFinal sixT sixS 0 1)=4 := by decide
