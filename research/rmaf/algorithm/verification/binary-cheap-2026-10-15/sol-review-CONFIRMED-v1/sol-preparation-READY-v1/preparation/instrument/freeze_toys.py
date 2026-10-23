#!/usr/bin/env python3
"""One-shot Std/Lean-only toy source and policy freeze, no compilation."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent.parent;S=P/'toy-src'
M={
'ToyClean':'''import OriginAudit
namespace ToyClean
structure Packet where
  value : Nat
private def hidden : Nat := 11
def ordinary : Nat := 7
theorem harmless : True := True.intro
end ToyClean
''',
'ToyUnused':'''import OriginAudit
axiom outside_namespace_unused : False
namespace ToyUnused
theorem harmless : True := True.intro
end ToyUnused
''',
'ToyPrivate':'''import OriginAudit
namespace ToyPrivate
structure Packet where
  value : Nat
private axiom hidden : Nat
private noncomputable def hiddenUse : Nat := hidden
theorem harmless : True := True.intro
end ToyPrivate
''',
'ToyExternal':'''import OriginAudit
namespace ToyExternal
axiom importedBad : False
end ToyExternal
''',
'ToyUseExternal':'''import OriginAudit
import ToyExternal
namespace ToyUseExternal
theorem contaminated : False := ToyExternal.importedBad
end ToyUseExternal
''',
'ToyRestriction':'''import OriginAudit
namespace ToyRestriction
structure Restriction where
  value : Nat
end ToyRestriction
''',
'ToyDepthRestriction':'''import OriginAudit
namespace ToyDepthRestriction
structure DepthRestriction where
  value : Nat
end ToyDepthRestriction
''',
'ToySource':'''import OriginAudit
import ToyRestriction
namespace ToyRoute
structure Packet where
  value : Nat
private def hiddenId (r : ToyRestriction.Restriction) : ToyRestriction.Restriction := r
def identity (r : ToyRestriction.Restriction) : ToyRestriction.Restriction := r
def projected (r : ToyRestriction.Restriction) : Nat := r.value
theorem harmless : True := True.intro
end ToyRoute
'''}
adapter=[['import ToyRestriction\n','import ToyDepthRestriction\n'],['ToyRestriction.Restriction','ToyDepthRestriction.DepthRestriction']]
a=M['ToySource']
for old,new in adapter:a=a.replace(old,new)
M['ToyAdapted']=a;M['ToyTampered']=a.replace(':= r.value',':= r.value + 1')
records=[]
for n,body in M.items():
 (S/(n+'.body')).write_text(body);(S/(n+'.lean')).write_text(body+'\nrun_cmd ReleasedAudit.emit ["'+n+'"]\n')
 (S/('Import'+n+'.lean')).write_text('import OriginAudit\nimport '+n+'\nrun_cmd ReleasedAudit.emit ["'+n+'"]\n')
 records.append({'module':n,'body_sha256':hashlib.sha256(body.encode()).hexdigest(),'source_sha256':hashlib.sha256((S/(n+'.lean')).read_bytes()).hexdigest(),
                 'observer_sha256':hashlib.sha256((S/('Import'+n+'.lean')).read_bytes()).hexdigest()})
policy={'phase':'PRE-CANDIDATE','candidate_compilation':False,'allowed_imports':['Lean','Std','OriginAudit']+list(M),
 'modules':list(M),'standard_axiom_allowlist':['propext','Classical.choice','Quot.sound'],
 'expected_accept':{n:n not in ['ToyUnused','ToyPrivate','ToyExternal','ToyUseExternal'] for n in M},
 'expected_clean_declarations':19,'expected_unused_declarations':2,'expected_adapter':adapter,
 'expected_reject_mutations':['zero inventory','missing origin','missing private declaration','duplicate origin row','unused external-namespace custom axiom','private custom axiom','foreign custom axiom closure','changed body despite identical declaration names'],
 'all_origins_required':True,'public_prefix_filter_forbidden':True,'source_import_full_inventory_equality_required':True,
 'origin_and_normalized_private_generated_fingerprints_required':True}
(P/'toy-policy-v1.json').write_text(json.dumps(policy,indent=2)+'\n')
(P/'toy-freeze-v1.json').write_text(json.dumps({'frozen_before_compilation':True,'modules':records,'audit_support_sha256':hashlib.sha256((S/'OriginAudit.lean').read_bytes()).hexdigest(),
 'policy_sha256':hashlib.sha256((P/'toy-policy-v1.json').read_bytes()).hexdigest()},indent=2)+'\n')
print('Frozen',len(M),'Lean/Std-only source/import twins and exact Restriction-to-DepthRestriction adapter controls.')
