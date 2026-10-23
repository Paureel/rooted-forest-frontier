#!/usr/bin/env python3
"""One-shot supplement for the only custom datatype names at the runtime
reference boundary. Uses the retained audit instrument and capped pilot."""
from pathlib import Path
import gzip,hashlib,importlib.util,json,time
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());J=D/'resume_20261016T083330Z';F=R/json.loads((J/'FINAL-ROOT-v1.json').read_text())['root']
def mod(n,p):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
P=mod('pilot_extra',D/'pilot.py');P.O=F;I=mod('instrument_extra',D/'instrument.py')
stamp=str(time.time_ns());name='ProviderDatatypeAudit'+stamp;Q=F/('datatype-audit-'+stamp);Q.mkdir();wanted=['RMAF','ForestColorWork']
(F/(name+'.lean')).write_text(I.source(['ProviderResumeControls'],wanted,Q));P.run(name,False,0);extra=I.parse(Q,wanted,F)
a=json.loads((F/'receipt.json').read_text());a['audits'].append({'module':name,'directory':str(Q.relative_to(R)),'producers':wanted,'occurrences':len(extra),'status':'PASS_STORED_CUSTOM_DATATYPE_BOUNDARY'})
rows={}
for batch in a['audits']:
 for n in batch['producers']:
  with gzip.open(R/batch['directory']/(n+'.json.gz'),'rt') as f:
   for row in json.load(f):
    assert row['name'] not in rows;rows[row['name']]=row
p=F/'runtime-body-audit.json';old=json.loads(p.read_text());(F/'runtime-body-audit-before-datatypes.json').write_bytes(p.read_bytes())
banned={'GenericForest.ScalarBits.decode','GenericForest.ScalarBits.encode'}|{'GenericForest.BinaryProvider.'+x for x in ['labelValue','blockValue','forestValue','treeValue','sourcesValue','targetValue','forestOptionValue']}
seen=set();todo=list(old['registered_runtime_definitions']);boundary=set()
while todo:
 n=todo.pop()
 if n in seen:continue
 assert n not in banned;seen.add(n);row=rows.get(n)
 if row is None:boundary.add(n);continue
 if row['kind']=='theorem':continue
 for ref in row['references']:
  assert ref not in banned,(n,ref)
  if ref not in seen:todo.append(ref)
assert not any(n.startswith(('RMAF.','Universal233.','GenericForest.')) for n in boundary),sorted(boundary)
old.update(visited_names=sorted(seen),unexpanded_boundary=sorted(boundary),occurrences=len(rows),custom_runtime_boundary='ALL_STORED_CUSTOM_REFERENCES_RESOLVED',boundary_note='Every custom reference in the registered runtime closure has a stored occurrence record. Remaining boundary names are Lean standard primitives. No nativeIR/compiler correspondence theorem is claimed.')
p.write_text(json.dumps(old,indent=2)+'\n')
(F/'receipt-before-datatypes.json').write_bytes((F/'receipt.json').read_bytes());(F/'receipt.json').write_text(json.dumps(a,indent=2)+'\n');(J/'AUDIT-RESULT-v1.json').write_text(json.dumps({k:v for k,v in a.items() if k!='origins'},indent=2)+'\n')
(F/'provenance'/('resume_audit_complete-'+hashlib.sha256(Path(__file__).read_bytes()).hexdigest()[:16]+'.py')).write_bytes(Path(__file__).read_bytes())
print('DATATYPE_AUDIT',len(extra),'extra;',len(rows),'total;',len(seen),'runtime references;',len(boundary),'standard boundary names')
