import StdClean
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let requested : List Name := [`StdClean,`NeverImported]
  if requested.isEmpty then throwError "FRESH_EMPTY_INVENTORY"
  let allowed : List Name := [`propext,`Classical.choice,`Quot.sound]
  let mut seen : List Name := []
  let mut bad : Nat := 0
  for (name,info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let origin := env.allImportedModuleNames[index.toNat]!
      if requested.contains origin then
        seen := origin :: seen
        let axioms ← collectAxioms name
        let nonstandard := axioms.toList.filter (fun x => !allowed.contains x)
        let rejected := info.isAxiom || info.isUnsafe || !nonstandard.isEmpty
        if rejected then bad := bad + 1
        logInfo m!"FRESH|{origin}|{name}|{info.isAxiom}|{info.isUnsafe}|{String.intercalate "," (axioms.toList.map Name.toString)}|{rejected}"
  for origin in requested do
    let n := (seen.filter (· == origin)).length
    logInfo m!"FRESH_COUNT|{origin}|{n}"
    if n == 0 then throwError m!"FRESH_MISSING_ORIGIN {origin}"
  logInfo m!"FRESH_BAD|{bad}"
  if bad > 0 then throwError "FRESH_AUDIT_REJECT"
