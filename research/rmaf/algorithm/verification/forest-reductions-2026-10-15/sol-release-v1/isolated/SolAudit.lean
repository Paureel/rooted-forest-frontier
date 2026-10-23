import Lean
open Lean Elab Command

def solSourceModules : List String := ["RMAF", "StateRestriction", "StateEmbedding", "StatePartition", "State", "Singleton", "Removal", "Forward", "LeafClear", "Reverse", "CherryGraph", "CherryTopology", "Endpoint", "Replacement", "Contraction", "BlockPartition", "QuotientGeometry", "QuotientTopology", "StateContract", "Expansion", "StateExpand", "GraphControls", "CompletionConsumers", "Controls", "Consumers"]

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
  let producers := env.constants.toList.filterMap fun (n, ci) =>
    if solSourceModules.contains (solOrigin env n) then
      match ci with
      | .defnInfo _ => some n
      | _ => none
    else none
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
    else if !(s == "Init" || s.startsWith "Init." || s == "Std" || s.startsWith "Std." || s == "Lean" || s.startsWith "Lean." || s == "SolAudit") then
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
      if kind == "theorem" then
        let ty ← liftTermElabM fun _ => Meta.ppExpr ci.type
        liftIO <| IO.println <| "TYPE\t" ++ tag.getString ++ "\t" ++ toString n ++ "\t" ++ (Json.str ty.pretty).compress
