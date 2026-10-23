import Interface
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let names : List Name := [`RMAF,`Geometry,`Bridge,`Restriction,`Cluster,`Descendant,`Forest,`Surgery,`Count,`Parents,`Exchange,`SourceEdge,`Selector,`Interface]
  let standards : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut found : List Name := []
  let mut bad : Nat := 0
  for entry in env.constants.toList do
    let n := entry.1
    let info := entry.2
    if let some index := env.getModuleIdxFor? n then
      let origin := env.allImportedModuleNames[index.toNat]!
      if names.contains origin then
        found := origin :: found
        let dependencies ← collectAxioms n
        let forbidden := dependencies.toList.filter (fun a => !standards.contains a)
        let invalid := info.isAxiom || info.isUnsafe || !forbidden.isEmpty
        if invalid then bad := bad + 1
        logInfo m!"FRESH|{origin}|{n}|{info.isAxiom}|{info.isUnsafe}|{String.intercalate "," (dependencies.toList.map Name.toString)}|{invalid}"
  for module in names do
    let count := (found.filter (· == module)).length
    logInfo m!"FRESH_COUNT|{module}|{count}"
    if count == 0 then throwError m!"FRESH_MISSING_ORIGIN {module}"
  logInfo m!"FRESH_BAD|{bad}"
  if bad > 0 then throwError "FRESH_AUDIT_REJECT"
