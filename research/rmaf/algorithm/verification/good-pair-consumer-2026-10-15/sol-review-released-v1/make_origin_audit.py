#!/usr/bin/env python3
"""Prepared module-origin audit, grouped to scan the imported environment once."""
import json
from pathlib import Path
P=Path(__file__).resolve().parent;ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience')
order=json.loads((ROOT/'results/algorithm-universal233-pair-assembly-20261015T093218Z/certificate.json').read_text())['positive_order']
base='''import Lean
open Lean Elab Command
namespace ReleasedAudit

def kind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .inductInfo _ => "inductive"

def emit (wanted : List String) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let names := env.constants.fold (fun acc n _ =>
    let origin := match env.getModuleIdxFor? n with
      | none => env.mainModule
      | some i => env.allImportedModuleNames[i.toNat]!
    if wanted.contains origin.toString then acc.push n else acc) (#[] : Array Name)
  let names := names.qsort (fun a b => a.toString < b.toString)
  let mut rows : Array Json := #[]
  for n in names do
    let origin := match env.getModuleIdxFor? n with
      | none => env.mainModule
      | some i => env.allImportedModuleNames[i.toNat]!
    let some ci := env.find? n | throwError "missing declaration {n}"
    let axs ← Lean.collectAxioms n
    rows := rows.push (Json.mkObj [("name",toJson n.toString),("origin",toJson origin.toString),
      ("kind",toJson (kind ci)),("private",toJson (Lean.privateToUserName? n).isSome),
      ("user_name",toJson ((Lean.privateToUserName? n).getD n).toString),
      ("axioms",toJson (axs.toList.map Name.toString))])
  liftIO <| IO.println ("AUDIT_JSON " ++ (Json.mkObj [("requested_origins",toJson wanted),("declarations",Json.arr rows),("count",toJson rows.size)]).compress)
end ReleasedAudit
'''
(P/'src/ReleasedAuditBase.lean').write_text(base)
for name,mods in [('AuditFrozenToys',['ToyClean','ToyUnusedAxiom','ToyPrivateAxiom','ToyUseExternal']),('AuditScientific',order)]:
 (P/'src'/f'{name}.lean').write_text('import ReleasedAuditBase\n'+''.join('import '+m+'\n' for m in mods)+'\nrun_cmd ReleasedAudit.emit ['+', '.join('"'+m+'"' for m in mods)+']\n')
