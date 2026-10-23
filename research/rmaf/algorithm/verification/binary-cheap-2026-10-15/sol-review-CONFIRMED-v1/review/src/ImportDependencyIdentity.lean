import AuditScientific
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.println ("IMPORTS_JSON " ++ (toJson (env.allImportedModuleNames.toList.map Name.toString)).compress)
