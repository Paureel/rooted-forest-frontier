-- One-shot suffix inventory, compiled helper avoids kernel-reducing a whole env fold.
import Ordinary
import Lean.Elab.Command
open Lean Elab Command
def ownAllowedNames : CommandElabM Unit := do
  let env ← getEnv
  env.constants.forM fun n _ => do
    if n.getString! == "proper" then logInfo m!"ALLOWED_NAME {n}"
run_cmd ownAllowedNames
#print RMAF.DepthOne.proper
#print Universal233.CoreGraph.DepthOne.proper
#print Universal233.OrdinaryDispatch.DepthOne.proper
example : (2 : Nat) = 2 := rfl
