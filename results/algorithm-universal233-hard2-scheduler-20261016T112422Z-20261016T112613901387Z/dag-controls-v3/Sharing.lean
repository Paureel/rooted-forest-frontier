import BoundedExprDAG
open Lean Elab Command BoundedExprDAG
run_cmd do
 let mut e:=mkConst `Nat.zero
 for _ in [:25] do e:=mkApp e e
 let action:Dump (Nat×Nat×Nat):=do
  let a←expr e
  let x←expr (.lam `x (.sort .zero) (.bvar 0) .default)
  let y←expr (.lam `y (.sort .zero) (.bvar 0) .default)
  return (a,x,y)
 let ((a,x,y),s)←liftIO <| action.run {dir:="/Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-hard2-scheduler-20261016T112422Z-20261016T112613901387Z/dag-controls-v3/sharing",stem:="dag"}
 unless a=25 && x != y && s.nodes=30 do throwError m!"DAG_SHARING_OR_BINDER_CONTROL|{a}|{x}|{y}|{s.nodes}"
 logInfo "DAG_SHARING_BINDER_PASS"
