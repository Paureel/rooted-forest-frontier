-- Constrained name inventory for lower restriction/embedding facts only.
-- No source or theorem body is printed or executed.
import Ordinary
import ProperJobs
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  env.constants.forM fun n _ => do
    let s := n.toString
    if "RestrictionBridge.".isPrefixOf s &&
        (["rooted", "minimal", "restrict", "leaves", "subtree"].any fun p => decide ((s.splitOn p).length > 1)) then
      if !(decide ((s.splitOn "cherry").length > 1)) then
        logInfo m!"LOWER_NAME {n}"
