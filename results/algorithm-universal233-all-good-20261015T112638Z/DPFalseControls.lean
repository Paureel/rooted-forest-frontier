import ConsumerControls
open RMAF ForestState AllGoodDP AllGoodControls
example : decideBudget (some quartet) crossed 0 = true := by decide
example : decideBudget (some six) three 1 = true := by decide
example : additionalCost [n (l 0) (l 1),n (l 2) (l 3)]
    (candidate (some quartet) [n (l 0) (l 1),n (l 2) (l 3)]) =
    changes (solve [0,1] (owner [n (l 0) (l 1),n (l 2) (l 3)]) quartet) := by decide
example : (blocks (.node 1 (.node 1 (.leaf 0 0) (.leaf 1 0))
    (.node 1 (.leaf 2 0) (.leaf 3 0)))).length = 5 := by decide
