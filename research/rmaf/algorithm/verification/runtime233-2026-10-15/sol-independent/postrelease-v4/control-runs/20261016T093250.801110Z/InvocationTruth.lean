import OrdinaryCallBound
open RMAF ForestState Universal233
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
example : (ordinaryStepTrace FastOrdinary.solve 0 (.leaf 0) (.leaf 1)).queries.length=0 := by decide +kernel
example : ordinaryCallNodes 0 (.leaf 0) (.leaf 1)=1 := by decide +kernel
example : ordinaryCallNodes 0 (.leaf 0) (.leaf 0)=1 := by decide +kernel
example : queryWork (fun _ _ _=>3) [((.leaf 0,.leaf 1),0),((.leaf 0,.leaf 1),0)]=6 := by decide +kernel
example : callNodeFactor=1024 := by decide +kernel
