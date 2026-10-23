-- One-shot exact stored-dependency traversal. Never prints imported proof bodies.
import Boundary26
import Controls13
import Lean
open Lean Elab Command
def auditForbidden : Array String := #[
 "Universal233.CherryBranching.actual_pendant_safety", "Universal233.CherryBranching.actual_high_safety",
 "actual_t1_pendant_exchange", "T1Exchange", "ordinary_branches_cover", "found_globally_minimum",
 "OrdinaryDispatch.FastOrdinary.solve_exact", "exactOneRule", "exactHighRule", "high_rule_if_dichotomy",
 "one_rule_if_exchange", "IndependentPaid.CherryForestDichotomy", "sorryAx"]
def auditRoots : Array Name := #[
 `OwnHigh.cherry_distinct, `OwnHigh.agreement_singleton_or_shared,
 `OwnHigh.agreement_source_cherry, `OwnHigh.refines_of_no_crossing,
 `OwnHigh.literal_consumer, `OwnHigh.refinesB_correct,
 `OwnHigh.c01, `OwnHigh.c02, `OwnHigh.c03, `OwnHigh.c04, `OwnHigh.c05,
 `OwnHigh.c06, `OwnHigh.c07, `OwnHigh.c08, `OwnHigh.c09, `OwnHigh.c10]
def auditKind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient-primitive"
  | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
def isForbiddenName (n : Name) : Bool := auditForbidden.any fun s => s.isInfixOf n.toString
def auditClosure : CommandElabM Unit := do
  let env ← getEnv
  let mut todo := auditRoots
  let mut seen : NameHashSet := {}
  let mut rows : Array Json := #[]
  let mut ownBodies : Array Json := #[]
  let mut axioms : Array String := #[]
  let mut bad : Array String := #[]
  let mut unknown : Array String := #[]
  let mut reused : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if isForbiddenName n then
      bad := bad.push n.toString
      continue
    let some ci := env.find? n | unknown := unknown.push n.toString; continue
    let moduleName := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.header.mainModule
    let mut refs := ci.getUsedConstantsAsSet.toArray
    if let .recInfo rv := ci then
      for rule in rv.rules do refs := refs ++ rule.rhs.getUsedConstants
    todo := todo ++ refs
    let value := ci.value? (allowOpaque := true)
    if auditKind ci == "axiom" then axioms := axioms.push n.toString
    if (auditKind ci == "theorem" || auditKind ci == "definition" || auditKind ci == "opaque") && value.isNone then
      unknown := unknown.push (n.toString ++ ": missing stored body")
    rows := rows.push (Json.mkObj [
      ("name",toJson n.toString), ("module",toJson moduleName.toString),
      ("kind",toJson (auditKind ci)), ("stored_body",toJson value.isSome),
      ("refs",toJson (refs.map Name.toString))])
    let own := "OwnHigh.".isPrefixOf n.toString
    let standard := ["Init", "Std", "Lean"].any fun p => p.isPrefixOf moduleName.toString
    if own then
      ownBodies := ownBodies.push (Json.mkObj [
        ("name",toJson n.toString), ("module",toJson moduleName.toString),
        ("type_raw",toJson (reprStr ci.type)),
        ("body_raw",toJson (value.map reprStr)), ("kind",toJson (auditKind ci))])
    else if !standard then
      reused := reused.push n
  let path := "/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/verification/fast-ordinary-solver-2026-10-15/fresh-high-20261016T104344Z/"
  IO.FS.writeFile (path ++ "DEPENDENCY-GRAPH-v1.json") ((Json.mkObj [
    ("roots",toJson (auditRoots.map Name.toString)), ("rows",toJson rows),
    ("axioms",toJson axioms), ("forbidden_reached",toJson bad), ("unknown",toJson unknown)]).pretty)
  IO.FS.writeFile (path ++ "OWN-STORED-BODIES-v1.json") ((toJson ownBodies).pretty)
  logInfo m!"AUDIT counts: {rows.size} declarations; {ownBodies.size} own bodies; {reused.size} imported domain constants"
  logInfo m!"AUDIT axioms: {axioms}"
  logInfo m!"AUDIT forbidden: {bad}; unknown: {unknown}"
  for n in reused do
    let ci := env.find! n
    logInfo m!"REUSED {n} [{auditKind ci}] : {ci.type}"
run_cmd auditClosure
#print axioms OwnHigh.agreement_singleton_or_shared
#print axioms OwnHigh.agreement_source_cherry
#print axioms OwnHigh.literal_consumer
