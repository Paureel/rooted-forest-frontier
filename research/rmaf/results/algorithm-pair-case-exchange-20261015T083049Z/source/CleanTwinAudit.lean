import Controls
import CleanTwin
import Lean
open Lean Elab Command

/- One-shot originating-module inventory, including generated/private declarations. -/
run_cmd do
  let env ← getEnv
  let modules : List Name := [`RMAF,`Geometry,`Bridge,`Restriction,`Cluster,`Descendant,
    `Forest,`Surgery,`Count,`Parents,`Exchange,`Controls,`CleanTwin]
  let allowed : List Name := [`propext,`Classical.choice,`Quot.sound]
  let mut totals : List (Name × Nat) := modules.map (fun n => (n,0))
  let mut bad : Nat := 0
  for (n,ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.allImportedModuleNames[idx.toNat]!
      if modules.contains mod then
        totals := totals.map (fun (m,c) => if m == mod then (m,c+1) else (m,c))
        let axs ← collectAxioms n
        let forbidden := axs.filter (fun a => !allowed.contains a)
        logInfo m!"ORIGIN|{mod}|{n}|AXIOMS:{String.intercalate "," (axs.toList.map toString)}|UNSAFE:{ci.isUnsafe}"
        if !forbidden.isEmpty || ci.isUnsafe then bad := bad + 1
  for (m,c) in totals do
    logInfo m!"MODULE_COUNT|{m}|{c}"
    if c == 0 then throwError m!"Missing originating-module declarations: {m}"
  logInfo m!"FORBIDDEN_DECLARATIONS|{bad}"
  if bad != 0 then throwError "Originating-module axiom/unsafe audit rejected"
