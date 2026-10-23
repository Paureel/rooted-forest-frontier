import WeightedSourceSubtotal
open RMAF OrdinaryDispatch.FullSourceWork
example : sourceSubtotal (fun _ _ _=>7) 2 (.leaf 0) (.leaf 1)=0 := by rw [sourceSubtotal_eq]; decide +kernel
