import Witness01
import Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let expected : List Name := [`Witness01]
 for i in [:env.header.moduleNames.size] do
   let producer := env.header.moduleNames[i]!
   let path ← liftIO <| findOLean producer
   logInfo m!"PATH|{producer}|{path}"
   if expected.contains producer then
     let data := env.header.moduleData[i]!
     unless data.constants.size == data.constNames.size do
       throwError m!"PRODUCER_NAME_LENGTH_MISMATCH|{producer}"
     logInfo m!"SUMMARY|{producer}|{data.constants.size}"
     for j in [:data.constants.size] do
       let ci := data.constants[j]!
       unless data.constNames[j]! == ci.name do
         throwError m!"PRODUCER_NAME_ROW_MISMATCH|{producer}|{j}"
       let kind := match ci with
         | .axiomInfo _ => "axiom"
         | .defnInfo _ => "definition"
         | .thmInfo _ => "theorem"
         | .opaqueInfo _ => "opaque"
         | .quotInfo _ => "quotient"
         | .inductInfo _ => "inductive"
         | .ctorInfo _ => "constructor"
         | .recInfo _ => "recursor"
       let resolved := match env.getModuleIdxFor? ci.name with
         | none => "UNATTRIBUTED"
         | some idx => toString env.header.moduleNames[idx.toNat]!
       if resolved == "UNATTRIBUTED" then
         throwError m!"UNATTRIBUTED_PRODUCER|{producer}|{ci.name}"
       let refs := ci.getUsedConstantsAsSet.toList
       let mut axs : List Name := []
       for dep in refs do
         let da ← collectAxioms dep
         axs := (axs ++ da.toList).eraseDups
       let row := Json.mkObj [
         ("producer",toJson (toString producer)),("index",toJson j),
         ("name",toJson (toString ci.name)),("resolved_origin",toJson resolved),
         ("kind",toJson kind),("type",toJson (reprStr ci.type)),
         ("body",toJson (ci.value?.map reprStr)),
         ("references",toJson (refs.map toString)),
         ("axiom_references",toJson (axs.map toString))]
       logInfo m!"PRODUCERJSON|{row.compress}"
       if kind == "axiom" then
         unless ci.name == `Classical.choice || ci.name == `propext || ci.name == `Quot.sound do
           throwError m!"REJECT_DIRECT_CUSTOM_AXIOM|{producer}|{j}|{ci.name}"
       for ax in axs do
         unless ax == `Classical.choice || ax == `propext || ax == `Quot.sound do
           throwError m!"REJECT_DEPENDENCY_CUSTOM_AXIOM|{producer}|{j}|{ci.name}|{ax}"
