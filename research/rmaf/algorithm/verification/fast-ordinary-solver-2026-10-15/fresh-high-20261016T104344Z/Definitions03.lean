-- One-shot exact suffix discovery using a bounded accumulator, no proof bodies.
import Ordinary
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
    if ["proper", "CherryAt", "pendantOriginal"].contains n.getString! then acc.push n else acc
  for n in names do logInfo m!"ALLOWED_NAME {n}"
#print RMAF.restrict
#print RMAF.sameShape
#print RMAF.minimalVertices
#print Universal233.CoreGraph.subtree
#print Universal233.HardParent.vertices
#print Universal233.HardParent.subtreeLabels
