import BoundedExprDAG
open Lean Elab Command BoundedExprDAG
run_cmd do
 let action:Dump Unit:=emit (toJson (String.ofList (List.replicate (5*1024*1024) 'x')))
 let _←liftIO <| action.run {dir:="/Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-hard2-scheduler-20261016T112422Z-20261016T112613901387Z/dag-controls-v3/oversize",stem:="dag"}
