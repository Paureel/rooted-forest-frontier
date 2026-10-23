-- One-shot exact suffix name inventory and allowed definition inspection.
import Ordinary
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    if ["proper", "CherryAt", "pendantOriginal"].contains n.getString! then
      logInfo m!"ALLOWED_NAME {n}"
#print Universal233.DepthOne.proper
#print Universal233.CoreGraph.CherryAt
#print Universal233.HardParent.pendantOriginal
#print RMAF.restrictionAgrees
#print RMAF.pairwiseEmbeddings
#print RMAF.partitionCheck
