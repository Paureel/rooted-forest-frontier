import OrdinaryCallBound
open RMAF ForestState Universal233
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
example : queryWork (fun _ _ _=>3) [((.leaf 0,.leaf 1),0),((.leaf 0,.leaf 1),0)]=3 := by decide +kernel
