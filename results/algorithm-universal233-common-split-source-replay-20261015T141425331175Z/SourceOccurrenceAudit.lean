import SourceFinal
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted : List Name := [`RMAF, `CoreGraph, `Geometry, `Bridge, `Composition, `SourceBridge, `CherryCoarsening, `CoreProgram, `CoreInvariants, `Contraction, `Normalization, `InitialLift, `Suppression, `EraseLift, `Origins, `Branches, `CutRecords, `FullTransport, `Coverage, `Entrypoint, `OutputBudget, `ColorBudget, `ColorSteps, `RawMass, `RationalMass, `ParentColors, `OriginalGraph, `Display, `Regions, `History, `Realization, `OwnerCover, `CutCoverage, `InitialCoverage, `Cost, `ValidPartition, `WholeSource, `Requests, `OwnershipBase, `ChainAssembly, `SourceValidity, `ForestOutputs, `WholeColors, `OriginalColors, `WholeMass, `PaidAssembly, `Executable, `Endpoint, `Restriction, `PendantExclusion, `Refinement, `Components, `Safety, `HardConsumer, `HardPaid, `HardForest, `Selector, `ExchangeRestriction, `Cluster, `Descendant, `Forest, `Surgery, `Count, `Parents, `Exchange, `SourceEdge, `Interface, `SideColors, `PairConsumer, `VertexPair, `GoodPair, `RankCost, `MinimumUnique, `TailMass, `ColorClasses, `Probe, `Work, `ProbeWork, `FourProbe, `KeptGraph, `KeptRun, `KeptParent, `KeptConsumers, `Pretest, `GroupRestriction, `GroupEmbedding, `GroupPartition, `Lemmas, `Reconstruction01, `Optimality01, `Witness01, `LiteralControls, `BinaryEdge, `CheapPartition, `TargetGeometry, `Continuation, `LocalOne, `PretestConsumer, `SelectedContinuation, `Symmetry, `SelectedHigh, `BothProgram, `Crossing, `Controls, `Rename, `GroupState, `GroupStateFacts, `GroupCost, `GroupForward, `GroupReconstruction, `GroupDefs, `GroupForwardProof, `GroupReverseProof, `GroupCostProof, `GroupPriority, `OutputDefs, `Materialize, `Equivalence, `CrossingCount, `Marked, `Clip, `Deletion, `MarkerSingleton, `MarkerBounds, `Port, `OriginalPort, `PortSingleton, `MixedPort, `CutHull, `ForestMerge, `MarkedLift, `StableMarker, `ClipCount, `Contract, `PortContract, `Projection, `OriginalSides, `OriginalProjection, `EdgeSides, `ProjectedPartition, `ProjectedForest, `MarkedProjection, `OriginalGlue, `HeadPermutation, `MarkerBlock, `MarkerNormal, `MergeStable, `CountOriginal, `MinimumIdentity, `DerivedMinimum, `GraphControls, `CallerDefs, `ChosenOwner, `LiteralNormal, `LiteralMerge, `PickMerge, `CallerSetup, `PaidDefs, `InsideBudget, `PaidExact, `ProperJobs, `LiteralExtension, `OutsideDefs, `OutsideExact, `CallerResources, `GuardedDefs, `GuardedExact, `CallerControls, `PaidControls, `OutsideControls, `GuardedControls, `GuardRefusalControls, `CallerFinal, `SourceDefs, `SourceControls, `SourceBoundary, `ActualCuts, `BuildSetup, `BuildComplete, `BuildIdentity, `SourceProgram, `OutsideOne, `ThreeOutside, `SourceNonrefusal, `BuilderControls, `ActualFrameControls, `SourceFinal]
  let allowed : List Name := [`Classical.choice,`Quot.sound,`propext]
  let mut counts : Array Json := #[]
  let mut bad : Array Json := #[]
  for i in [:env.header.moduleNames.size] do
    let producer := env.header.moduleNames[i]!
    if wanted.contains producer then
      let data := env.header.moduleData[i]!
      unless data.constants.size == data.constNames.size do throwError "PRODUCER_ARRAY_LENGTH_MISMATCH"
      let mut rows : Array Json := #[]
      let filename := producer.toString ++ ".json"
      counts := counts.push (Json.mkObj [("producer",toJson producer.toString),("count",toJson data.constants.size),("file",toJson filename)])
      for j in [:data.constants.size] do
        let ci := data.constants[j]!
        let stored := data.constNames[j]!
        unless stored == ci.name do throwError "PRODUCER_NAME_MISMATCH"
        let kind := match ci with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
          | .inductInfo _ => "inductive"
        let body := ci.value? true
        let bodyText := match body with | some e => reprStr e | none => "<none>"
        let mut refs := ci.type.getUsedConstants.toList
        if let some e := body then refs := refs ++ e.getUsedConstants.toList
        refs := refs.eraseDups
        let mut ax : List Name := []
        if ci.isAxiom then ax := [ci.name]
        for n in refs do ax := ax ++ (← collectAxioms n).toList
        ax := ax.eraseDups
        let resolved := match env.getModuleIdxFor? ci.name with
          | some k => env.header.moduleNames[k.toNat]!.toString
          | none => "<unresolved>"
        rows := rows.push (Json.mkObj [("producer",toJson producer.toString),("index",toJson j),
          ("stored_name",toJson stored.toString),("actual_name",toJson ci.name.toString),
          ("resolved_origin",toJson resolved),("kind",toJson kind),
          ("type",toJson (reprStr ci.type)),("body",toJson bodyText),("has_body",toJson body.isSome),
          ("direct_references",toJson (refs.map Name.toString)),("axiom_references",toJson (ax.map Name.toString))])
        if (ci.isAxiom && !allowed.contains ci.name) || ax.any (fun n => !allowed.contains n) then
          bad := bad.push (Json.mkObj [("producer",toJson producer.toString),("name",toJson ci.name.toString),("kind",toJson kind),("axioms",toJson (ax.map Name.toString))])
      liftIO <| IO.FS.writeFile ("/Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-common-split-source-replay-20261015T141425331175Z/producer-records" ++ "/" ++ filename) (Json.arr rows).pretty
  liftIO <| IO.FS.writeFile ("/Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-common-split-source-replay-20261015T141425331175Z/producer-records" ++ "/index.json") (Json.mkObj [("producer_counts",Json.arr counts),("rejects",Json.arr bad)]).pretty
  if !bad.isEmpty then throwError m!"REJECT_PRODUCER_OCCURRENCE|{bad.size}"
  logInfo m!"PRODUCER_OCCURRENCE_PASS|{counts.size}"
