import GroupConsumerControls
import Lean
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
