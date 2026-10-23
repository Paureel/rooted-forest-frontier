import Lean
open Lean Elab Command
elab "#sol_compiler_extras " names:str : command => do
  let e ← getEnv
  let wanted := names.getString.splitOn ","
  for i in [:e.header.moduleNames.size] do
    let producer := toString e.header.moduleNames[i]!
    if wanted.contains producer then
      let extra := e.header.moduleData[i]!.extraConstNames
      for j in [:extra.size] do
        let n := extra[j]!
        let resolved := match e.getModuleIdxFor? n with
          | some k => toString e.header.moduleNames[k.toNat]!
          | none => "UNMAPPED"
        let visible := (e.find? n).isSome
        liftIO <| IO.println <| "EXTRA\t" ++ (Json.mkObj [
          ("producer",toJson producer),("occurrenceIndex",toJson j),
          ("name",toJson (toString n)),("resolvedOrigin",toJson resolved),
          ("hasKernelConstantInfo",toJson visible)]).compress
