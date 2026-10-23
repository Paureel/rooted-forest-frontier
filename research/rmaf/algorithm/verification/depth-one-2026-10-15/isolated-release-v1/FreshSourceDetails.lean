import RMAF
import Geometry
import Bridge
import Composition
import CoreGraph
import CherryCoarsening
import CoreProgram
import CoreInvariants
import SourceBridge
import Contraction
import Normalization
import InitialLift
import Suppression
import EraseLift
import Origins
import Branches
import CutRecords
import OriginalGraph
import Display
import Regions
import History
import Realization
import OwnerCover
import Coverage
import InitialCoverage
import Cost
import ValidPartition
import Restriction
import Embedding
import Partition
import Pretest
import Controls
import Lemmas
import Reconstruction01
import Optimality01
import Witness01
import Runtime01
import ConsumerControls
import SourceColorControls
import Lean
open Lean Elab Command
def freshRefs : Expr → List Name
 | .const n _ => [n]
 | .app f x => freshRefs f ++ freshRefs x
 | .lam _ t b _ => freshRefs t ++ freshRefs b
 | .forallE _ t b _ => freshRefs t ++ freshRefs b
 | .letE _ t v b _ => freshRefs t ++ freshRefs v ++ freshRefs b
 | .mdata _ e => freshRefs e
 | .proj _ _ e => freshRefs e
 | _ => []
run_cmd do
 let env ← getEnv
 let modules : List Name := [`RMAF,`Geometry,`Bridge,`Composition,`CoreGraph,`CherryCoarsening,`CoreProgram,`CoreInvariants,`SourceBridge,`Contraction,`Normalization,`InitialLift,`Suppression,`EraseLift,`Origins,`Branches,`CutRecords,`OriginalGraph,`Display,`Regions,`History,`Realization,`OwnerCover,`Coverage,`InitialCoverage,`Cost,`ValidPartition,`Restriction,`Embedding,`Partition,`Pretest,`Controls,`Lemmas,`Reconstruction01,`Optimality01,`Witness01,`Runtime01,`ConsumerControls,`SourceColorControls]
 for n in modules do
  let path ← liftIO <| findOLean n
  logInfo m!"PATH|{n}|{path}"
 for (n,i) in env.constants.toList do
  if let some idx := env.getModuleIdxFor? n then
   let origin := env.allImportedModuleNames[idx.toNat]!
   if modules.contains origin then
    let kind := match i with
     | .thmInfo _ => "theorem"
     | .defnInfo _ => "definition"
     | .opaqueInfo _ => "opaque"
     | .axiomInfo _ => "axiom"
     | _ => "inductive/constructor/recursor/quotient"
    let j := Json.mkObj [("name",toJson n.toString),("origin",toJson origin.toString),
      ("type",toJson (reprStr i.type)),("type_hash",toJson i.type.hash.toNat),
      ("body_hash",toJson ((i.value? true).map (fun e => e.hash.toNat))),("kind",toJson kind)]
    logInfo m!"DETAIL|{j.compress}"
 let mut pending : List Name := [`Universal233.DepthOne.pretest01]
 let mut seen : List Name := []
 while !pending.isEmpty do
  let n := pending.head!
  pending := pending.tail!
  if !seen.contains n then
   seen := n :: seen
   if let some i := env.find? n then
    let origin := match env.getModuleIdxFor? n with
      | none => `Unknown
      | some idx => env.allImportedModuleNames[idx.toNat]!
    logInfo m!"CALL|{n}|{origin}"
    if modules.contains origin then
     if let some value := i.value? true then pending := freshRefs value ++ pending
