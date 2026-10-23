import NumericPrecontrols
import NumericLocal
import NumericRule5
import NumericStep
import NumericReach
import NumericSizes
import NumericStateBounds
import NumericEntries
import NumericActualEntries
import NumericSourceBinding
import NumericOperands
import NumericInterface
import NumericControls
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let wanted : List Name := [`NumericPrecontrols, `NumericLocal, `NumericRule5, `NumericStep, `NumericReach, `NumericSizes, `NumericStateBounds, `NumericEntries, `NumericActualEntries, `NumericSourceBinding, `NumericOperands, `NumericInterface, `NumericControls]
 for i in [:env.header.moduleNames.size] do
  let producer := env.header.moduleNames[i]!
  let path ← liftIO <| findOLean producer
  logInfo m!"PATH|{producer}|{path}"
  if wanted.contains producer then
   let data := env.header.moduleData[i]!
   unless data.constants.size == data.constNames.size do throwError "HEADER_ARRAY_MISMATCH"
   logInfo m!"COUNT|{producer}|{data.constants.size}"
   for j in [:data.constants.size] do
    let ci := data.constants[j]!
    let kind := match ci with
      | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor" | .inductInfo _ => "inductive"
    logInfo m!"NAME|{producer}|{j}|{ci.name}|{kind}"
