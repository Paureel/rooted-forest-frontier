import Lean
import SelectedHigh
open Lean Elab Command
namespace RuntimeReview
partial def visit (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: ns =>
    if seen.contains n then visit env ns seen else
    let seen := seen.insert n
    let next := match env.find? n with
      | some (.defnInfo d) => d.value.getUsedConstants.toList
      | some (.opaqueInfo d) => d.value.getUsedConstants.toList
      | _ => []
    visit env (next ++ ns) seen

def binders : Expr → List String
  | .forallE n _ b _ => n.toString :: binders b
  | _ => []
end RuntimeReview

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := [`Universal233.DepthOne.pretest01, `Universal233.RankConsumer.fourAccepted,
    `Universal233.BinaryCheap.cheapColor, `Universal233.PairAssembly.sideOutputs,
    `PairGeometry.choose, `Universal233.CoreProgram.generate]
  let mut records : Array Json := #[]
  for root in roots do
    let some ci := env.find? root | throwError "missing runtime root {root}"
    let seen := RuntimeReview.visit env [root] {}
    let names := seen.toArray.qsort Name.lt
    let own := names.filter (fun n => match env.getModuleIdxFor? n with
      | none => false
      | some i => !(env.allImportedModuleNames[i.toNat]!.toString.startsWith "Lean") &&
          !(env.allImportedModuleNames[i.toNat]!.toString.startsWith "Init") &&
          !(env.allImportedModuleNames[i.toNat]!.toString.startsWith "Std"))
    records := records.push (Json.mkObj [("root",toJson root.toString),
      ("binders",toJson (RuntimeReview.binders ci.type)),("all_value_dependencies",toJson (names.toList.map Name.toString)),
      ("scientific_value_dependencies",toJson (own.toList.map Name.toString))])
  liftIO <| IO.println ("RUNTIME_JSON " ++ (Json.arr records).compress)
