import Lean

/- Fresh one-shot producer-occurrence scanner. Own v1 helper structure reused;
no other verifier source read. Stored arrays precede coalescing. -/
open Lean Elab Command

private def scientificNames : Array String := #["RMAF","Geometry","QueryCaller","GroupRestriction","Bridge","CoreGraph","Executable","ExchangeRestriction","QuerySpecification","GroupEmbedding","Composition","CherryCoarsening","CoreProgram","Selector","Cluster","Pretest","QueryBudgets","GroupPartition","SourceBridge","CoreInvariants","Descendant","QueryMass","GroupCost","GroupState","Contraction","Endpoint","Forest","Work","QueryWork","GroupForward","GroupStateFacts","Normalization","Restriction","Surgery","GroupReconstruction","InitialLift","PendantExclusion","Count","GroupDefs","Suppression","Refinement","Parents","GroupForwardProof","EraseLift","Exchange","GroupReverseProof","Origins","SourceEdge","GroupCostProof","Branches","Interface","GroupPriority","CutRecords","FullTransport","OriginalGraph","OutputDefs","Coverage","Display","Components","OutputControls","Materialize","Entrypoint","Regions","Safety","Equivalence","OutputBudget","History","Permutation","ColorBudget","Realization","ColorSteps","OwnerCover","RawMass","CutCoverage","RationalMass","InitialCoverage","ParentColors","Cost","WholeColors","ValidPartition","OriginalColors","KeptGraph","WholeSource","WholeMass","KeptRun","Lemmas","Requests","KeptParent","Reconstruction01","OwnershipBase","KeptConsumers","Optimality01","ChainAssembly","Witness01","SourceValidity","MafCaller","ForestOutputs","RankCost","LocalSlots","PaidAssembly","MinimumUnique","Regional","HardConsumer","TailMass","Indexing","HardPaid","ColorClasses","OriginalReconstruction","HardForest","Probe","OriginalCaller","SideColors","ProbeWork","OriginalPaid","PairConsumer","FourProbe","VertexPair","GoodPair","LiteralControls","BinaryEdge","CheapPartition","TargetGeometry","Continuation","LocalOne","PretestConsumer","SelectedContinuation","Symmetry","OppositeGroups","SelectedHigh","LocalCertificates","ConsumerControls","ResidualConsumer","BothProgram","ActualConsumers","BothPrecontrols","Crossing","CoreCover","Planner","PlannerControls","PlannerFacts","PlannerSources","Dispatcher","DispatchControls","ExecutionFacts","ForestContract","OrdinaryBridge","RetainedBridge","RetainedLower","PlannerGeometry","CheapPlannerCover","PlanCover","QueryTrace","ActualBadSlots","MassAssembly","CheapPlanMass","PlanActualMass","CallDecrease","PlannerWork","ExecutionWork","BothConsumers"]

private def knd : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def ss (xs : Array String) : Json := .arr (xs.map Json.str)

private def val (c : ConstantInfo) : Json :=
  match c.value? (allowOpaque := true) with
  | some e => .str (reprStr e)
  | none => .null

elab "audit_scientific! " destination:str : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  unless mods.size == env.header.moduleData.size do
    throwError "producer-name/data alignment unavailable"
  let mut stored : Array Json := #[]
  let mut resolved : Array Json := #[]
  let mut rejected : Array String := #[]
  let mut producerInventories : Array Json := #[]
  let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for i in [:mods.size] do
    let producer := mods[i]!
    if scientificNames.contains producer.toString then
      let d := env.header.moduleData[i]!
      unless d.constNames.size == d.constants.size do
        throwError "stored declaration arrays misaligned in {producer}"
      producerInventories := producerInventories.push <| Json.mkObj [
        ("producer", .str producer.toString),
        ("stored_count", toJson d.constants.size),
        ("olean_path", .str (← liftIO (findOLean producer)).toString),
        ("imports", ss (d.imports.map fun x => x.module.toString)),
        ("compiler_extra_names", ss (d.extraConstNames.map Name.toString))]
      for j in [:d.constants.size] do
        let c := d.constants[j]!
        let n := d.constNames[j]!
        unless c.name == n do throwError "stored name/body mismatch"
        let resolvedInfo := env.find? n
        let resolvedOrigin := match env.getModuleIdxFor? n with
          | some idx => mods[idx.toNat]!.toString
          | none => "UNRESOLVED"
        let resolvedKind := match resolvedInfo with
          | some info => knd info
          | none => "UNRESOLVED"
        let mut axs : Array String := #[]
        for dep in c.getUsedConstantsAsSet.toArray do
          if (env.find? dep).isNone then
            rejected := rejected.push s!"unresolved-dependency:{producer}:{n}:{dep}"
          else
            for ax in (← collectAxioms dep) do
              axs := axs.push ax.toString
              if !standard.contains ax then
                rejected := rejected.push s!"resolved-dependency-axiom:{producer}:{n}:{ax}"
        if knd c == "axiom" then
          rejected := rejected.push s!"stored-direct-axiom:{producer}:{n}"
        stored := stored.push <| Json.mkObj [
          ("producer", .str producer.toString), ("index", toJson j),
          ("name", .str n.toString), ("kind", .str (knd c)),
          ("type", .str (reprStr c.type)), ("body", val c),
          ("resolved_origin", .str resolvedOrigin), ("resolved_kind", .str resolvedKind),
          ("dependencies", ss (c.getUsedConstantsAsSet.toArray.map Name.toString)),
          ("resolved_dependency_axioms", ss axs)]
  for (n,c) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let origin := mods[idx.toNat]!
      if scientificNames.contains origin.toString then
        resolved := resolved.push <| Json.mkObj [
          ("name", .str n.toString), ("origin", .str origin.toString),
          ("kind", .str (knd c)), ("type", .str (reprStr c.type)), ("body", val c)]
  for mod in mods do
    let s := mod.toString
    unless scientificNames.contains s || s == "ScientificAudit" || s == "Init" || s.startsWith "Init." || s == "Std" || s.startsWith "Std." || s == "Lean" || s.startsWith "Lean." do
      rejected := rejected.push s!"unexpected-nonstandard-module:{s}"
  let out := Json.mkObj [
    ("all_modules", ss (mods.map Name.toString)),
    ("producer_inventories", .arr producerInventories),
    ("stored_occurrences", .arr stored), ("resolved_names", .arr resolved),
    ("imports", ss (env.header.imports.map fun x => x.module.toString)),
    ("dependency_scope", .str "stored type/body direct references; closure resolved in merged environment; every scientific producer direct axiom scanned"),
    ("rejected", ss rejected)]
  liftIO <| IO.FS.writeFile destination.getString out.pretty
  logInfo m!"SCIENTIFIC_PRODUCERS stored={stored.size} resolved={resolved.size} rejected={rejected.size}"
