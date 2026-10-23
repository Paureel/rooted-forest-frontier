import CoreInvariants
import CherryCoarsening
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let ns := (env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)
  let ns := (ns.filter (fun n => (`Universal233).isPrefixOf n || (`RMAF).isPrefixOf n)).eraseDups
  let ns := ns.mergeSort Name.quickLt
  for n in ns do logInfo m!"DECL|{n}"
  for n in ns do
    let axs ← collectAxioms n
    logInfo m!"AUDIT|{n}|{axs.toList}"
    for a in axs do
      unless a == `propext || a == `Quot.sound || a == `Classical.choice do
        throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
