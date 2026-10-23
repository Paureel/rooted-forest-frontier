import ClassificationControls
open RMAF Universal233.Rule5Classification Universal233.Rule5Classification.Controls
open Universal233.Rule5Local Universal233.Rule5Local.Pre Universal233.CherryBranching
example : selectLarge largeT largeS 0 1 = none := by decide
example : selectSizeTwo twoT twoS 0 1 = none := by decide
example : selectOutside outsideT outsideS 0 1 = none := by decide
example : refinesCheck largeF (pendantPartition largeS 0 1) = true := by decide
example : (fiveChildren twoS 0 1 9 10).map Child.paid = [1,1,1,1,1] := by decide
example : (selectLarge (mirror largeT) (mirror largeS) 1 0) = some [] := by decide
