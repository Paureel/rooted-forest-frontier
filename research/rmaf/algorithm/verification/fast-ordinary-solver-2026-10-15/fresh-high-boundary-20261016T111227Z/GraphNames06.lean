-- Names only for generic lower path/hull/subtree facts in three fixed namespaces.
-- Excludes cherry/pendant/safety/coverage/exchange/exactness/minimum names.
import SourceBasics05
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  env.constants.forM fun n _ => do
    let s := n.toString
    if ["Integration.","Universal233.CoreGraph.","VertexGeometry."].any (fun p => p.isPrefixOf s) &&
        (["minimal","hull","Hull","span","path","Path","subtree"].any fun p => decide ((s.splitOn p).length > 1)) &&
        !(["cherry","Cherry","pendant","Pendant","safe","Safe","cover","Cover","exchange","Exchange","exact","Exact","minimum","Minimum"].any fun p => decide ((s.splitOn p).length > 1)) then
      logInfo m!"LOWER_NAME {n}"
