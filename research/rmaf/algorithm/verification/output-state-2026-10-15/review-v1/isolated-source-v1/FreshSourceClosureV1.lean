import FreshEveryOutputConsumerV1
import Lean
open Lean Elab Command
def freshExprNames : Expr → List Name
 | .const n _ => [n]
 | .app a b => freshExprNames a ++ freshExprNames b
 | .lam _ t b _ => freshExprNames t ++ freshExprNames b
 | .forallE _ t b _ => freshExprNames t ++ freshExprNames b
 | .letE _ t v b _ => freshExprNames t ++ freshExprNames v ++ freshExprNames b
 | .mdata _ e => freshExprNames e
 | .proj _ _ e => freshExprNames e
 | _ => []
run_cmd do
 let env ← getEnv
 let modules : List Name := [`RMAF,`GroupRestriction,`GroupEmbedding,`GroupPartition,`GroupCost,`GroupForward,`Geometry,`Bridge,`Composition,`GroupReconstruction,`GroupState,`GroupStateFacts,`GroupDefs,`GroupForwardProof,`GroupReverseProof,`GroupCostProof,`GroupPriority,`CoreGraph,`SourceBridge,`CherryCoarsening,`CoreProgram,`CoreInvariants,`Contraction,`Normalization,`InitialLift,`Suppression,`EraseLift,`Origins,`Branches,`CutRecords,`FullTransport,`Coverage,`Entrypoint,`OutputBudget,`ColorBudget,`ColorSteps,`RawMass,`RationalMass,`ParentColors,`OriginalGraph,`Display,`Regions,`History,`Realization,`OwnerCover,`CutCoverage,`InitialCoverage,`Cost,`ValidPartition,`WholeSource,`Requests,`OwnershipBase,`ChainAssembly,`SourceValidity,`ForestOutputs,`WholeColors,`OriginalColors,`WholeMass,`PaidAssembly,`Executable,`Endpoint,`Restriction,`PendantExclusion,`Refinement,`Components,`Safety,`HardConsumer,`HardPaid,`HardForest,`Selector,`ExchangeRestriction,`Cluster,`Descendant,`Forest,`Surgery,`Count,`Parents,`Exchange,`SourceEdge,`Interface,`SideColors,`PairConsumer,`VertexPair,`GoodPair,`RankCost,`MinimumUnique,`TailMass,`ColorClasses,`Probe,`Work,`ProbeWork,`FourProbe,`KeptGraph,`KeptRun,`KeptParent,`KeptConsumers,`Pretest,`Lemmas,`Reconstruction01,`Optimality01,`Witness01,`LiteralControls,`BinaryEdge,`CheapPartition,`TargetGeometry,`Continuation,`LocalOne,`PretestConsumer,`SelectedContinuation,`Symmetry,`SelectedHigh,`ConsumerControls,`OutputDefs,`OutputControls,`Materialize,`Equivalence,`Permutation,`OppositeGroups,`LocalCertificates,`ResidualConsumer,`ActualConsumers,`FreshActualReadoutsV2,`FreshEveryOutputConsumerV1,`FreshActualCleanV1]
 for root in ([`OutputState.sourceForest,`ForestGroups.owned,`ForestState.agrees] : List Name) do
  let mut todo := [root]
  let mut seen : List Name := []
  let mut used : List Name := []
  while !todo.isEmpty do
   let n := todo.head!
   todo := todo.tail!
   if !seen.contains n then
    seen := n :: seen
    if let some idx := env.getModuleIdxFor? n then
     if modules.contains env.allImportedModuleNames[idx.toNat]! then
      used := n :: used
      if let some i := env.find? n then
       if let some v := i.value? then todo := freshExprNames v ++ todo
   if seen.length > 5000 then throwError "OPEN_CLOSURE_CAP"
  logInfo m!"CLOSURE|{root}|{String.intercalate "," (used.map Name.toString)}"
