import ToyClean
import Lean
open Lean Elab Command
run_cmd do
  let path ← liftIO <| findOLean `ToyClean
  logInfo m!"PATH|{path}"
