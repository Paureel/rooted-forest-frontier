import CommonControls
open OrdinaryDispatch OrdinaryDispatch.CommonControls RMAF ForestState
example : (runCommonCherry callback T S c 0).map (fun F=>(agreement T S F,F.length))=some (true,2) := by cbv
example : (leaves (contract c.a c.b (commonFresh T) T)).length=(leaves T).length := by decide
