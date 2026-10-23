#!/usr/bin/env python3
"""One-shot source creation of preregistered Lean/Std-only clean/false toys."""
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent.parent
b=p/'toy-src';(b/'bodies').mkdir(exist_ok=True)
modules={
 'ToyClean':'''import AuditSupport
namespace ToyClean
structure Packet where
  value : Nat
private def hidden : Nat := 11
def ordinary : Nat := 7
theorem harmless : True := True.intro
end ToyClean
''',
 'ToyUnusedAxiom':'''import AuditSupport
axiom outside_namespace_unused : False
namespace ToyUnusedAxiom
theorem harmless : True := True.intro
end ToyUnusedAxiom
''',
 'ToyPrivateAxiom':'''import AuditSupport
namespace ToyPrivateAxiom
structure Packet where
  value : Nat
private axiom hidden : Nat
private def hiddenUse : Nat := hidden
theorem harmless : True := True.intro
end ToyPrivateAxiom
''',
 'ToyExternal':'''import AuditSupport
namespace ToyExternal
axiom importedBad : False
end ToyExternal
''',
 'ToyUseExternal':'''import AuditSupport
import ToyExternal
namespace ToyUseExternal
theorem contaminated : False := ToyExternal.importedBad
end ToyUseExternal
''',
 'ToyRestriction':'''import AuditSupport
namespace ToyRestriction
structure Restriction where
  value : Nat
end ToyRestriction
''',
 'ToyExchangeRestriction':'''import AuditSupport
namespace ToyExchangeRestriction
structure ExchangeRestriction where
  value : Nat
end ToyExchangeRestriction
''',
 'ToyRestrictionSource':'''import AuditSupport
import ToyRestriction
namespace ToyRoute
structure Packet where
  value : Nat
private def hiddenId (r : ToyRestriction.Restriction) : ToyRestriction.Restriction := r
def identity (r : ToyRestriction.Restriction) : ToyRestriction.Restriction := r
def projected (r : ToyRestriction.Restriction) : Nat := r.value
theorem harmless : True := True.intro
end ToyRoute
''',
 'ToyCoverage':'''import AuditSupport
namespace ToyCoverage
def flag : Bool := true
end ToyCoverage
''',
 'ToyExistingCoverage':'''import AuditSupport
namespace ToyExistingCoverage
def flag : Bool := true
end ToyExistingCoverage
''',
 'ToyCoverageSource':'''import AuditSupport
import ToyCoverage
namespace ToyCoverageRoute
private def hidden : Bool := ToyCoverage.flag
def identity : Bool := ToyCoverage.flag
theorem harmless : True := True.intro
end ToyCoverageRoute
''',
}
substitutions=[('import ToyRestriction\n','import ToyExchangeRestriction\n'),('ToyRestriction.Restriction','ToyExchangeRestriction.ExchangeRestriction')]
a=modules['ToyRestrictionSource']
for old,new in substitutions:a=a.replace(old,new)
modules['ToyExchangeAdapted']=a
modules['ToyExchangeTampered']=a.replace(':= r.value',':= r.value + 1')
c=modules['ToyCoverageSource'].replace('import ToyCoverage\n','import ToyExistingCoverage\n').replace('ToyCoverage.flag','ToyExistingCoverage.flag')
modules['ToyCoverageAdapted']=c
modules['ToyCoverageTampered']=c.replace('def identity : Bool := ToyExistingCoverage.flag','def identity : Bool := !ToyExistingCoverage.flag')
records=[]
for name,body in modules.items():
 (b/'bodies'/f'{name}.lean').write_text(body)
 (b/f'{name}.lean').write_text(body+f'\naudit_local "{name}"\n')
 records.append({'module':name,'body_sha256':hashlib.sha256(body.encode()).hexdigest(),'instrumented_sha256':hashlib.sha256((b/f'{name}.lean').read_bytes()).hexdigest()})
(p/'toy-source-freeze-v1.json').write_text(json.dumps({'created_before_compilation':True,'modules':records,'support_sha256':hashlib.sha256((b/'AuditSupport.lean').read_bytes()).hexdigest(),'candidate_compilation':False,'all_three_milestones':'OPEN'},indent=2)+'\n')
print('Frozen',len(records),'toy modules before compilation.')
