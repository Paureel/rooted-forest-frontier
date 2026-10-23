import PreControls
open RMAF ForestState AllGoodControls
example : additionalCost [n (l 0) (l 1),n (l 2) (l 3)] [[0,1],[2,3]] = 1 := by decide
example : agrees (some quartet) crossed [[0,2],[1,3]] = true := by decide
example : additionalCost crossed [[0,2],[1],[3]] = 0 := by decide

-- Three connected leafless B vertices, four isolated A leaf components.
-- The five raw monochromatic components include the empty B component.
example : ([[],[0],[1],[2],[3]].filter (fun b => !b.isEmpty)).length = 4 + 1 := by decide
