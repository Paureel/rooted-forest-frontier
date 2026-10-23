import Lean
open Lean Elab Command

def solSourceModules : List String := ["RMAF", "StateRestriction", "StateEmbedding", "StatePartition", "State", "ColorDP", "ColorRegions", "ActualProgram", "TargetEmbedding", "IsoTransport", "StateSoundness", "CoreGraph", "Geometry", "Bridge", "Composition", "SourceBridge", "CherryCoarsening", "CoreProgram", "CoreInvariants", "Contraction", "Normalization", "InitialLift", "Suppression", "EraseLift", "Origins", "Branches", "CutRecords", "OriginalGraph", "CutColoring", "FullTransport", "Coverage", "Entrypoint", "OutputBudget", "ColorBudget", "ColorSteps", "RawMass", "RationalMass", "ParentColors", "Display", "Regions", "History", "Realization", "OwnerCover", "CutCoverage", "InitialCoverage", "Cost", "ValidPartition", "WholeSource", "Requests", "OwnershipBase", "ChainAssembly", "SourceValidity", "RankCost", "MinimumUnique", "TailMass", "ColorClasses", "RecoveryProgram", "BlockColors", "Permutations", "Recovery", "LowerBound", "StateCost", "ExactMinimum"]

private def solOrigin (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => toString env.header.moduleNames[i.toNat]!
  | none => toString env.mainModule

private def solInheritedOrigin (env : Environment) (n : Name) : Option (String × String) := Id.run do
  let mut p := n.getPrefix
  for _ in [:n.getNumParts] do
    if p.isAnonymous then return none
    if let some i := env.getModuleIdxFor? p then
      let origin := toString env.header.moduleNames[i.toNat]!
      if solSourceModules.contains origin then return some (origin, toString p)
    p := p.getPrefix
  return none

elab "#sol_force_all" : command => do
  let env ← getEnv
  let producers : List Name := []
  let env' ← liftTermElabM fun _ => do
    for n in producers do
      let _ ← Meta.getEqnsFor? n
    getEnv
  setEnv env'
  liftIO <| IO.println s!"FORCED\t{producers.length}"

elab "#sol_candidate_inventory " tag:str : command => do
  let env ← getEnv
  for mod in env.header.moduleNames do
    let s := toString mod
    if solSourceModules.contains s then
      let path ← liftIO <| findOLean mod
      let real ← liftIO <| IO.FS.realPath path
      liftIO <| IO.println <| "MODULE\t" ++ tag.getString ++ "\t" ++ s ++ "\t" ++ real.toString
    else if !(s == "Init" || s.startsWith "Init." || s == "Std" || s.startsWith "Std." || s == "Lean" || s.startsWith "Lean." || s == "SolResolvedV1" || s == "SolResolvedV2") then
      throwError "unmapped imported module {mod}"
  let locals ← liftIO <| env.getLocalConstantInfos
  let mut rows := env.constants.toList
  for c in locals do
    if !rows.any (fun r => r.1 == c.name) then rows := (c.name,c.constInfo.get) :: rows
  for (n, ci) in rows do
    let raw := solOrigin env n
    let (origin, adapter) := if (env.getModuleIdxFor? n).isNone then
      match solInheritedOrigin env n with
      | some (m,p) => (m,"generated-prefix:" ++ p)
      | none => (raw,"direct")
      else (raw,"direct")
    if solSourceModules.contains origin then
      let kind := match ci with
        | .axiomInfo _ => "axiom"
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "definition"
        | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quot"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
      let axs ← liftCoreM <| collectAxioms n
      liftIO <| IO.println <| "ROW\t" ++ tag.getString ++ "\t" ++ toString n ++ "\t" ++ origin ++ "\t" ++ kind ++ "\t" ++ String.intercalate "," (axs.toList.map toString) ++ "\t" ++ raw ++ "\t" ++ adapter
      let valueRefs := match ci.value? true with | some v => v.getUsedConstants.toList.map toString | none => []
      liftIO <| IO.println <| "REFS\t" ++ tag.getString ++ "\t" ++ (Json.mkObj [
        ("name",toJson (toString n)),("origin",toJson origin),("rawOrigin",toJson raw),("adapter",toJson adapter),
        ("kind",toJson kind),("typeRefs",toJson (ci.type.getUsedConstants.toList.map toString)),("valueRefs",toJson valueRefs)]).compress
      if kind == "theorem" && (toString n).startsWith "AllGoodDP." then
        let ty ← liftTermElabM fun _ => Meta.ppExpr ci.type
        liftIO <| IO.println <| "TYPE\t" ++ tag.getString ++ "\t" ++ toString n ++ "\t" ++ (Json.str ty.pretty).compress
