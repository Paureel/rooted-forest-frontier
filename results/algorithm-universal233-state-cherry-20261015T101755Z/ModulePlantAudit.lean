import PlantModel
import CompletionConsumers
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : List Name := [`RMAF, `StateRestriction, `StateEmbedding, `StatePartition, `State, `Singleton, `Removal, `Forward, `LeafClear, `Reverse, `CherryGraph, `CherryTopology, `GraphControls, `Endpoint, `Replacement, `Contraction, `BlockPartition, `QuotientGeometry, `QuotientTopology, `StateContract, `Expansion, `StateExpand, `CompletionConsumers, `PlantModel]
  for mod in env.header.moduleNames do
    let path ← liftIO <| findOLean mod
    logInfo m!"PATH|{mod}|{path}"
  let ns := (env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)
  let ns := (ns.filter fun n =>
    match env.getModuleIdxFor? n with
    | some idx => modules.contains env.header.moduleNames[idx.toNat]!
    | none => false).eraseDups
  for n in ns do
    let some idx := env.getModuleIdxFor? n | throwError "missing module origin"
    let mod := env.header.moduleNames[idx.toNat]!
    logInfo m!"MODULE|{mod}|{n}"
  for n in ns do
    let axs ← collectAxioms n
    logInfo m!"MODAUDIT|{n}|{String.intercalate "," (axs.toList.map toString)}"
    for a in axs do
      unless a == `propext || a == `Quot.sound || a == `Classical.choice do
        throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
