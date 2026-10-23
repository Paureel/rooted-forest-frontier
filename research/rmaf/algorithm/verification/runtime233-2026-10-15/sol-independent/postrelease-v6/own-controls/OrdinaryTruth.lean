import OrdinarySimpleTreeSource
import Rule4CallerSource
open RMAF OrdinaryDispatch.FullSourceWork
example : sourceSubtotal (fun _ _ _=>7) 2 (.leaf 0) (.leaf 1)=7 := by rw [sourceSubtotal_eq]; decide +kernel
example : sourceSubtotal (fun _ _ r=>r+2) 10 (.leaf 0) (.leaf 1)=12 := by rw [sourceSubtotal_eq]; decide +kernel
example : simpleLocalDebit (.leaf 0) (.leaf 1) 1000=0 := by decide +kernel
example : simpleTreeSource 7 (.leaf 0) (.leaf 0)=0 := by rw [simpleTreeSource,sourceSubtotal_eq]; decide +kernel
example : (leafAddressMeter 0 (.node (.leaf 0) (.leaf 1))).value=some [false] := by decide +kernel
example : (leafAddressMeter 0 (.node (.leaf 0) (.leaf 1))).work=8 := by decide +kernel
example : (leafAddressMeter 1 (.node (.leaf 0) (.leaf 1))).work=12 := by decide +kernel
example : (leafAddressMeter 9 (.node (.leaf 0) (.leaf 1))).value=none := by decide +kernel
