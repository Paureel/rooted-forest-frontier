import PairWitness
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : List Name := [`RMAF, `CoreGraph, `CoreProgram, `PairWitness]
  let ns := ((env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)).filter fun n =>
    match env.getModuleIdxFor? n with
    | some idx => modules.contains env.header.moduleNames[idx.toNat]!
    | none => false
  let ns := ns.eraseDups
  for n in ns do
    let some idx := env.getModuleIdxFor? n | throwError "missing module"
    logInfo m!"MODULE|{env.header.moduleNames[idx.toNat]!}|{n}"
    let axs ← collectAxioms n
    logInfo m!"MODAUDIT|{n}|{axs.toList}"
    for a in axs do
      unless a == `propext || a == `Quot.sound || a == `Classical.choice do
        throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
