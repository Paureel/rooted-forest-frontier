import ForestColorWork
import Lean
open Lean Elab Command
deriving instance Repr for ConstantVal
deriving instance Repr for InductiveVal
deriving instance Repr for ConstructorVal
deriving instance Repr for RecursorRule
deriving instance Repr for RecursorVal
deriving instance Repr for AxiomVal
deriving instance Repr for QuotKind
deriving instance Repr for QuotVal
run_cmd do
 let env ← getEnv
 let wanted : Name := `ForestColorWork
 let mut rows : Array Json := #[]
 for i in [:env.header.moduleNames.size] do
  if env.header.moduleNames[i]! == wanted then
   let data := env.header.moduleData[i]!
   for ci in data.constants do
    let kind := match ci with
     | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
     | .axiomInfo _ => "axiom" | .quotInfo _ => "quotient" | _ => "skip"
    unless kind == "skip" do
     let text := match ci with
      | .inductInfo v => reprStr v | .ctorInfo v => reprStr v | .recInfo v => reprStr v
      | .axiomInfo v => reprStr v | .quotInfo v => reprStr v | _ => ""
     rows := rows.push (Json.mkObj [("name",toJson ci.name.toString),("kind",toJson kind),("full_constant_info",toJson text)])
 liftIO <| IO.FS.writeFile "/Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-full-source-20261016T085803Z-20261016T090439069784Z/author-audit-v3/MetadataChosen1.json" (Json.arr rows).pretty
