import CompletionControls
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[`RMAF, `Geometry, `Bridge, `Composition, `CoreGraph, `CherryCoarsening, `CoreProgram, `CoreInvariants, `SourceBridge, `Contraction, `Normalization, `InitialLift, `Suppression, `EraseLift, `Origins, `Branches, `CutRecords, `FullTransport, `Coverage, `Entrypoint, `OutputBudget, `ColorBudget, `ColorSteps, `RawMass, `RationalMass, `Controls, `OriginalGraph, `Display, `Regions, `History, `Realization, `OwnerCover, `CutCoverage, `InitialCoverage, `Cost, `ValidPartition, `CutControls, `ParentColors, `WholeSource, `Requests, `OwnershipBase, `ChainAssembly, `SourceValidity, `ForestOutputs, `AssemblyControls, `Executable, `Endpoint, `Restriction, `PendantExclusion, `Refinement, `Components, `Safety, `WholeColors, `OriginalColors, `WholeMass, `MassControls, `PaidAssembly, `HardConsumer, `HardPaid, `CompletionControls]
  let mut seen : Array Name := #[]
  for (n, info) in env.constants do
    if let some idx := env.getModuleIdxFor? n then
      let origin := env.header.moduleNames[idx.toNat]!
      if wanted.contains origin && !seen.contains n then
        seen := seen.push n
        let axioms ← collectAxioms n
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .thmInfo _ => "theorem"
          | _ => "other"
        logInfo m!"FRESH|{origin}|{n}|{kind}|{String.intercalate "," (axioms.toList.map toString)}"
  logInfo m!"FRESH_TOTAL|{seen.size}"
