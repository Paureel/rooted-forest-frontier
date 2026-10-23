-- One-shot exact allowed suffix names; no theorem statements or bodies.
import ProperJobs
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  env.constants.forM fun n _ => do
    match n with
    | .str _ "proper" => logInfo m!"ALLOWED_NAME {n}"
    | _ => pure ()
