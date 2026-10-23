import OriginA
open Lean Elab Command
run_cmd do
 let e ← getEnv
 for n in e.header.moduleNames do
  logInfo m!"ORIGIN|{n}"
example : originPaid = 7 := by decide +kernel
