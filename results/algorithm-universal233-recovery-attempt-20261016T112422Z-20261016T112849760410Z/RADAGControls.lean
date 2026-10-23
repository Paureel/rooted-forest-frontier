import RABoundedAudit
open Lean Elab Command
run_cmd do
 let e:=Expr.app (.const `Nat []) (.const `Nat [])
 let (root,s)←match exprDAG e {} with | .ok d=>pure d | .error e=>throwError e
 unless root==1 && s.nodes.size==2 do throwError "DAG_SHARING_CONTROL_FAILED"
 let app:=s.nodes[1]!
 let edges←match app.getObjValAs? (Array Nat) "children" with | .ok a=>pure a | .error e=>throwError e
 unless edges==#[0,0] do throwError "DAG_EDGE_CONTROL_FAILED"
 logInfo "DAG_SHARED_CHILD_CONTROL_PASS"
