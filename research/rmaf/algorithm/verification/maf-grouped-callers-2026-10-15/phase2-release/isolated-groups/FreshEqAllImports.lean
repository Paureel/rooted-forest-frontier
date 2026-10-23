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
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let some c := env.find? `RMAF.agreement.eq_1 | throwError "missing equation"
 logInfo m!"TYPE|{repr c.type}"
 match c with
 | .thmInfo t => logInfo m!"VALUE|{repr t.value}"
 | _ => throwError "expected theorem"
 let some idx := env.getModuleIdxFor? `RMAF.agreement.eq_1 | throwError "missing origin"
 logInfo m!"ORIGIN|{env.header.moduleNames[idx.toNat]!}"
