import RMAF
import Geometry
import Bridge
import Composition
import Restriction
import Embedding
import Partition
import Cost
import Forward
import Reconstruction
import Controls
import Consumers
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : List Name := [`RMAF,`Geometry,`Bridge,`Composition,`Restriction,`Embedding,`Partition,`Cost,`Forward,`Reconstruction,`Controls,`Consumers]
  for m in modules do
    let p ← liftIO <| findOLean m
    logInfo m!"PATH|{m}|{p}"
  for (n,i) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let origin := env.allImportedModuleNames[idx.toNat]!
      if modules.contains origin then
        let value := i.value? true
        let j := Json.mkObj [("origin",toJson origin.toString),("name",toJson n.toString),
          ("type",toJson (reprStr i.type)),("type_hash",toJson i.type.hash.toNat),
          ("body",toJson (value.map reprStr)),("body_hash",toJson (value.map (fun e => e.hash.toNat)))]
        logInfo m!"SIGNATURE|{j.compress}"
