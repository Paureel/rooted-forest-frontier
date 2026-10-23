import ClusterFreeWitness
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let mods : List Name := [`RMAF, `CoreGraph, `CoreProgram, `PairWitness, `ClusterFreeWitness]
 let names := (((env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)).filter fun n =>
   match env.getModuleIdxFor? n with
   | some i => mods.contains env.header.moduleNames[i.toNat]!
   | none => false).eraseDups
 for n in names do
   let some i := env.getModuleIdxFor? n | throwError "missing module"
   logInfo m!"MODULE|{env.header.moduleNames[i.toNat]!}|{n}"
   let ax ← collectAxioms n
   logInfo m!"MODAUDIT|{n}|{ax.toList}"
   for a in ax do
     unless a == `propext || a == `Quot.sound || a == `Classical.choice do
       throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
