-- One-shot safe exact suffix discovery in the pinned program module.
import Lean
open Lean
#eval do
  let env ← importModules #[{module := `FastSolve}] {} (trustLevel := 0)
  env.constants.forM fun n _ => do
    match n with
    | .str _ "proper" => IO.println s!"ALLOWED_NAME {n}"
    | _ => pure ()
