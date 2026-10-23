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
  let producers : List Name := [`RMAF.leaves, `RMAF.sameShape, `RMAF.restrict, `RMAF.Vertex, `RMAF.prependSide, `RMAF.rootedSpan, `RMAF.minimalVertices, `RMAF.disjointVertices, `RMAF.pairwiseEmbeddings, `RMAF.restrictionAgrees, `RMAF.partitionCheck, `RMAF.agreement, `RMAF.blocks, `RMAF.assignments, `RMAF.best, `RMAF.solve, `RMAF.Controls.leftTree, `RMAF.Controls.rightTree, `RMAF.Controls.exampleInstance, `RMAF.Controls.isolatedEndpoint, `RestrictionBridge.join, `RestrictionBridge.optionLeaves, `RestrictionBridge.Clear, `RestrictionBridge.contained, `RestrictionBridge.family, `RestrictionBridge.Refines, `ForestState.labels, `ForestState.targetEmbeddings, `ForestState.targetAgrees, `ForestState.proper, `ForestState.sourceCheck, `ForestState.agrees, `ForestState.additionalCost, `ForestState.cleanupTarget, `ForestState.cleanupSources, `ForestState.cleanupForest, `ForestState.cherry, `ForestState.contract, `ForestState.expand, `ForestState.cherryReady, `ForestState.contractBlock, `ForestState.expandBlock, `AllGoodDP.root, `AllGoodDP.erase, `AllGoodDP.delta, `AllGoodDP.changes, `AllGoodDP.edgeCost, `AllGoodDP.choose, `AllGoodDP.table, `AllGoodDP.solve, `AllGoodDP.vertices, `AllGoodDP.rowBound, `AllGoodDP.visits, `AllGoodDP.split, `AllGoodDP.rawBlocks, `AllGoodDP.blocks, `AllGoodDP.Mono, `AllGoodDP.owner, `AllGoodDP.allGood, `AllGoodDP.candidate, `AllGoodDP.run, `AllGoodDP.OptionIso, `Universal233.CoreGraph.subtree, `Universal233.CoreGraph.Valid, `Universal233.CoreGraph.LeafAt, `Universal233.CoreGraph.CherryAt, `Universal233.CoreGraph.Adj, `Universal233.CoreGraph.SingletonBlock, `Universal233.CoreGraph.Monochromatic, `VertexGeometry.Vertex, `VertexGeometry.Hull, `VertexGeometry.Prefix, `VertexGeometry.ProperPrefix, `VertexGeometry.region, `VertexGeometry.SameRegion, `VertexGeometry.jointRegion, `VertexGeometry.TwoJointRegions, `VertexGeometry.Occupies, `VertexGeometry.Clear, `VertexGeometry.DisjointParents, `VertexGeometry.lca, `VertexGeometry.median, `VertexGeometry.Convex, `VertexGeometry.Join, `VertexGeometry.Reach, `VertexGeometry.Nonempty, `VertexGeometry.selectedLeaves, `VertexGeometry.leafList, `VertexGeometry.regions, `VertexGeometry.jointColors, `VertexGeometry.colorLabel, `VertexGeometry.LabelMonochromatic, `VertexGeometry.findCommon, `VertexGeometry.commonPredicateCalls, `VertexGeometry.Refines, `VertexGeometry.Clears, `VertexGeometry.SourceEdge, `VertexGeometry.InSourceParent, `VertexGeometry.PieceHulls, `Universal233.Integration.HasCheckedSupport, `Universal233.Integration.checkedOwner, `Universal233.Integration.checkedSupport, `Universal233.Integration.checkedSourcePartition, `Universal233.CoreGraph.mergeOwner, `Universal233.CoreGraph.mergeSupport, `Universal233.CoreGraph.coarsenCherry, `Universal233.CoreGraph.Refines, `Universal233.CoreProgram.fromTree, `Universal233.CoreProgram.groups, `Universal233.CoreProgram.normalize, `Universal233.CoreProgram.erase, `Universal233.CoreProgram.mixedCherry, `Universal233.CoreProgram.choose, `Universal233.CoreProgram.combine, `Universal233.CoreProgram.prefixRoot, `Universal233.CoreProgram.attempt, `Universal233.CoreProgram.step, `Universal233.CoreProgram.run, `Universal233.CoreProgram.generate, `Universal233.CoreProgram.maxVisits, `Universal233.CoreProgram.Controls.crossed, `Universal233.CoreProgram.Controls.parity, `Universal233.CoreProgram.Controls.insertBy, `Universal233.CoreProgram.Controls.sortBy, `Universal233.CoreProgram.Controls.lexBy, `Universal233.CoreProgram.Controls.natLE, `Universal233.CoreProgram.Controls.canonicalPartition, `Universal233.CoreProgram.Controls.parts, `Universal233.CoreProgram.Controls.costs, `Universal233.CoreProgram.Controls.cherry3, `Universal233.CoreProgram.Controls.homColor, `Universal233.CoreProgram.payload, `Universal233.CoreProgram.PureGroups, `Universal233.CoreProgram.GoodCuts, `Universal233.CoreProgram.OutputShape, `Universal233.Integration.contractOwner, `Universal233.Integration.contractSupport, `Universal233.Integration.contractPartition, `Universal233.Integration.cherryProjection, `Universal233.Integration.skeleton, `Universal233.Integration.groupAt, `Universal233.Integration.GroupLeafAt, `Universal233.Integration.GroupedTransport, `Universal233.Integration.recolor, `Universal233.Integration.recolorPartition, `Universal233.Integration.retreePartition, `Universal233.Integration.initialPartition, `Universal233.Integration.erasureEmbedding, `Universal233.Integration.erasureTerminals, `Universal233.Integration.erasePartition, `Universal233.Integration.origins, `Universal233.Integration.gLeafErase_graph, `Universal233.Integration.FullyNormalized, `Universal233.Integration.nonrootOrigins, `Universal233.Integration.RootZeroOnly, `Universal233.Integration.CutsAvoid, `Universal233.Integration.SourceAttempt, `Universal233.CutRealization.Pre, `Universal233.CutRealization.Live, `Universal233.CutRealization.ResidualAdj, `Universal233.CutRealization.Region, `AllGoodDP.shade, `AllGoodDP.changeEdges, `Universal233.SourceCoverage.FullTransport, `Universal233.SourceCoverage.OwnerCover, `Universal233.SourceCoverage.SourceRefines, `Universal233.SourceCoverage.DetachedKept, `Universal233.SourceCoverage.ownerImage, `Universal233.SourceCoverage.RefinesBlocks, `Universal233.SourceCoverage.dedupNat, `Universal233.SourceCoverage.colors, `Universal233.SourceCoverage.colorCount, `Universal233.SourceCoverage.ColorCover, `Universal233.SourceCoverage.scaledMass, `Universal233.SourceCoverage.scaledQMass, `Universal233.SourceCoverage.rawQMass, `Universal233.Assembly.taggedColor, `Universal233.CutRealization.rootOrigin, `Universal233.CutRealization.Exact, `Universal233.CutRealization.LabelsValid, `Universal233.CutRealization.Difference, `Universal233.CutRealization.FinishOf, `Universal233.CutRealization.pairs, `Universal233.CutRealization.RealizedOutput, `Universal233.CutRealization.FullTransport, `Universal233.CutRealization.Tracked, `Universal233.CutRealization.blockRep, `Universal233.CutRealization.leafAddresses, `Universal233.CutRealization.colorCount, `Universal233.CutRealization.wholePayload, `Universal233.Assembly.targets, `Universal233.Assembly.localColor, `Universal233.Assembly.requestedColor, `Universal233.Assembly.ParentClears, `Universal233.Assembly.parentTag, `Universal233.Assembly.parentGroups, `Universal233.Assembly.BranchSolution, `Universal233.RankDichotomy.inputRank, `Universal233.RankDichotomy.RankFeasible, `Universal233.FinalCutRecovery.blockColor, `Universal233.FinalCutRecovery.inputCheck, `Universal233.FinalCutRecovery.recover, `Universal233.FinalCutRecovery.BlockPermutation, `Universal233.FinalCutRecovery.blockForKey, `AllGoodDP.decideBudget]
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
