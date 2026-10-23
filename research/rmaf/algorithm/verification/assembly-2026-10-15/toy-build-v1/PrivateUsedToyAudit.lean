import PrivateUsedToy
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n,c) in env.constants do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if m == `PrivateUsedToy then
        let axs ← collectAxioms n
        let k := match c with
          | .axiomInfo _ => "axiom"
          | .thmInfo _ => "theorem"
          | _ => "other"
        logInfo m!"TOY|{m}|{n}|{k}|{String.intercalate "," (axs.toList.map toString)}"
        count := count + 1
  logInfo m!"TOY_TOTAL|{count}"
