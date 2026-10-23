import FreshConsumer
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let some c := env.find? `Universal233.CoreProgram.generate.eq_1 | throwError "missing declaration"
  logInfo m!"DECL_TYPE|{repr c.type}"
  match c with
  | .thmInfo t => logInfo m!"DECL_VALUE|{repr t.value}"
  | _ => throwError "expected theorem"
