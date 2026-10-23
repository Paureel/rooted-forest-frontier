import Lean
open Lean Elab Command
elab "#closed_imports" : command => do
  let env ← getEnv
  for m in env.header.moduleNames do
    let s := toString m
    if s == "ToyClean" || s == "ClosedImports" ||
        s == "Init" || s.startsWith "Init." || s == "Std" || s.startsWith "Std." ||
        s == "Lean" || s.startsWith "Lean." then pure ()
    else throwError "unmapped source origin {m}"
  liftIO <| IO.println "CLOSED_IMPORTS_OK"
