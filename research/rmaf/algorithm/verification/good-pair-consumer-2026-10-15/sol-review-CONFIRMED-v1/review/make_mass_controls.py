#!/usr/bin/env python3
"""Direct compiled rawQMass checks on the same literal actual output lists."""
import hashlib,json
from pathlib import Path
p=Path(__file__).resolve().parent
s=(p/'src/CompiledControls.lean').read_text();assert s.count('def main : IO Unit := do')==1
s=s.replace('def main : IO Unit := do','def controlMain : IO Unit := do')
s+='''
def ratJson (r : Rat) : Json := Json.mkObj [("num",toJson r.num),("den",toJson r.den)]
def main : IO Unit := do
  for f in fixtures do
    if !f.knownFs.isEmpty then
      for q in List.range (f.qmax+1) do
        let os := goodPairOutputs f.S f.T f.A f.B q
        for c in ([2,(233:Rat)/100,3] : List Rat) do
          let mass := Universal233.SourceCoverage.rawQMass c os
          let bound := match PairGeometry.choose f.T f.A f.B with
            | some (.edge _) => c^(-3 : Int)
            | _ => c^(-3 : Int)+c^(-4 : Int)
          IO.println ((Json.mkObj [("id",toJson f.name),("q",toJson q),("c",ratJson c),
            ("mass",ratJson mass),("bound",ratJson bound),("le_bound",toJson (decide (mass<=bound)))]).compress)
  match fixtures with
  | f :: _ =>
    let os := goodPairOutputs f.S f.T f.A f.B f.qmax
    let dup := match os with
      | _ :: b :: _ => os ++ [b]
      | _ => []
    let clean := Universal233.SourceCoverage.rawQMass 2 os
    let bad := Universal233.SourceCoverage.rawQMass 2 dup
    IO.println ((Json.mkObj [("duplicate_control",toJson true),("clean_mass",ratJson clean),
      ("duplicate_mass",ratJson bad),("false_dedup_bound_rejected",toJson (decide (bad>clean)))]).compress)
  | [] => pure ()
'''
(p/'src/MassControlsIndependent.lean').write_text(s)
(p/'mass-control-source-freeze-v1.json').write_text(json.dumps({'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'expected_rational_value_rows':63,'expected_duplicate_rows':1,'clean_mass_c2':'3/16','duplicated_mass_c2':'5/16','created_before_execution':True,'no_scientific_candidate_source_edits':True},indent=2)+'\n')
