import Lean
import ToyClean
open Lean Elab Command
run_cmd do
  let p ← liftIO <| findOLean `ToyClean
  let p ← liftIO <| IO.FS.realPath p
  liftIO <| IO.println ("PATH\t" ++ p.toString)
