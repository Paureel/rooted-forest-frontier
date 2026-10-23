import Lean
open Lean Elab Command
/-- Force generated equation declarations and commit the resulting environment.
Ordinary #check may resolve them on a disposable elaboration branch. -/
elab "#sol_force_eqns " decl:ident : command => do
  let env' ← liftTermElabM fun _ => do
    let _ ← Meta.getEqnsFor? decl.getId
    getEnv
  setEnv env'

private def inheritedOrigin (env : Environment) (n : Name) : Option (String × String) := Id.run do
  let mut p := n.getPrefix
  for _ in [:n.getNumParts] do
    if p.isAnonymous then return none
    if let some i := env.getModuleIdxFor? p then
      return some (toString env.header.moduleNames[i.toNat]!, toString p)
    p := p.getPrefix
  return none

/-- Full checked table plus async local declarations; origin adapters are printed. -/
elab "#sol_inventory " tag:str : command => do
  let env ← getEnv
  let localInfos ← liftIO <| env.getLocalConstantInfos
  let mut rows := env.constants.toList
  for c in localInfos do
    if !rows.any (fun r => r.1 == c.name) then
      rows := (c.name, c.constInfo.get) :: rows
  for (n, ci) in rows do
    let rawOrigin := match env.getModuleIdxFor? n with
      | some i => toString env.header.moduleNames[i.toNat]!
      | none => toString env.mainModule
    let (origin, adapter) := if (env.getModuleIdxFor? n).isNone then
        match inheritedOrigin env n with
        | some (source, parent) => (source, "generated-prefix:" ++ parent)
        | none => (rawOrigin, "direct")
      else (rawOrigin, "direct")
    if origin.startsWith "Toy" then
      let kind := match ci with
        | .axiomInfo _ => "axiom"
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "definition"
        | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quot"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
      let axioms ← liftCoreM <| collectAxioms n
      liftIO <| IO.println <| "ROW\t" ++ tag.getString ++ "\t" ++ toString n ++ "\t" ++ origin ++ "\t" ++ kind ++ "\t" ++ String.intercalate "," (axioms.toList.map toString) ++ "\t" ++ rawOrigin ++ "\t" ++ adapter
