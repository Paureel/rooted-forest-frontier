import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.println ("STDLIB_IMPORT_JSON " ++ (toJson (env.allImportedModuleNames.toList.map Name.toString)).compress)
