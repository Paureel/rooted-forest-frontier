import RMAF
import GroupRestriction
import GroupEmbedding
import GroupPartition
import GroupCost
import GroupForward
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let mods : List Name := [`RMAF,`GroupRestriction,`GroupEmbedding,`GroupPartition,`GroupCost,`GroupForward]
 for (n,i) in env.constants.toList do
  if n.toString.startsWith "RMAF." then
   if let some idx := env.getModuleIdxFor? n then
    let origin := env.allImportedModuleNames[idx.toNat]!
    if origin != `RMAF && mods.contains origin then
     let axs ← collectAxioms n
     if i.isAxiom || i.isUnsafe || axs.toList.any (fun a => !([`propext,`Classical.choice,`Quot.sound] : List Name).contains a) then throwError "FORBIDDEN_GENERATED_BODY"
     let b := match i.value? (allowOpaque := true) with | some v => reprStr v | none => "NONE"
     let obj := Json.mkObj [("name",toJson n.toString),("origin",toJson origin.toString),("type",toJson (reprStr i.type)),("body",toJson b),("axioms",toJson (axs.toList.map Name.toString))]
     logInfo m!"GENERATED|{obj.compress}"
