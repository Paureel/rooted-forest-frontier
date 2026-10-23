import BranchMetadata
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let wanted : Name := `BranchMetadata
 let mut rows : Array Json := #[]
 for i in [:env.header.moduleNames.size] do
  if env.header.moduleNames[i]! == wanted then
   let data := env.header.moduleData[i]!
   for ci in data.constants do
    let kind := match ci with
     | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
     | .axiomInfo _ => "axiom" | .quotInfo _ => "quotient" | _ => "skip"
    unless kind == "skip" do
     rows := rows.push (Json.mkObj [("name",toJson ci.name.toString),("kind",toJson kind),("full_constant_info",toJson (reprStr ci))])
 liftIO <| IO.FS.writeFile "/Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-full-source-20261016T085803Z-20261016T090439069784Z/author-audit-v2/MetadataChosen0.json" (Json.arr rows).pretty
