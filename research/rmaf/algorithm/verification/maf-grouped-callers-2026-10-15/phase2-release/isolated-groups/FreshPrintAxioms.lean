import RMAF
import GroupRestriction
import GroupEmbedding
import GroupPartition
import GroupCost
import GroupForward
import Geometry
import Bridge
import Composition
import GroupReconstruction
import GroupState
import GroupStateFacts
import GroupControls
import GroupDefs
import GroupForwardProof
import GroupReverseProof
import GroupCostProof
import GroupPriority
import GroupConsumerControls
import FreshReadout
import FreshConsumer
import FreshFalseTwins
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let wanted : List Name := [`RMAF, `GroupRestriction, `GroupEmbedding, `GroupPartition, `GroupCost, `GroupForward, `Geometry, `Bridge, `Composition, `GroupReconstruction, `GroupState, `GroupStateFacts, `GroupControls, `GroupDefs, `GroupForwardProof, `GroupReverseProof, `GroupCostProof, `GroupPriority, `GroupConsumerControls, `FreshReadout, `FreshConsumer, `FreshFalseTwins]
 let mut count : Nat := 0
 for (n,ci) in env.constants do
  if let some idx := env.getModuleIdxFor? n then
   let m := env.header.moduleNames[idx.toNat]!
   if wanted.contains m then
    match ci with
    | .thmInfo _ =>
      logInfo m!"PRINT_ORIGIN|{m}|{n}"
      elabCommand (← `(command| #print axioms $(mkIdent n)))
      count := count+1
    | _ => pure ()
 logInfo m!"PRINT_TOTAL|{count}"
