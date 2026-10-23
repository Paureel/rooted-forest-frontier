#!/usr/bin/env python3
"""One-shot exact package replay. Same sources/compiler/instrument, zero
independent credit. Writes only a fresh replay directory; never rebuilds or
writes the sealed dependencies."""
from pathlib import Path
import datetime,gzip,hashlib,importlib.util,json,os,sys
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists())
F=R/(sys.argv[1] if len(sys.argv)>1 else (str(D.relative_to(R)) if (D/'receipt.json').exists() else json.loads((D/'resume_20261016T083330Z/FINAL-ROOT-v1.json').read_text())['root']))
a=json.loads((F/'receipt.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if (F/'manifest.json').exists():
 m=json.loads((F/'manifest.json').read_text())
 for e in m['immutable_files']:assert sha(R/e['path'])==e['sha256'],e['path']
Q=R/'results'/('algorithm-universal233-binary-resume-20261016T083330Z-replay-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));Q.mkdir()
def load(n,key):
 xs=[R/x['snapshot'] for x in a['origins'] if x['source'].endswith('/'+key)];p=xs[-1]
 s=importlib.util.spec_from_file_location(n,p);o=importlib.util.module_from_spec(s);s.loader.exec_module(o);return o
P=load('binary_replay_pilot','pilot.py');P.O=Q;I=load('binary_replay_instrument','instrument.py')
for p in F.glob('*.olean'):
 if p.stem not in set(a['source_modules']+['ProviderAuditGhost']):os.symlink(p.resolve(),Q/p.name)
results=[]
for n in a['source_modules']+['ProviderAuditGhost']:
 (Q/(n+'.lean')).write_bytes((F/(n+'.lean')).read_bytes());P.run(n,True,0);results.append({'module':n,'expected_exit':0,'source_rebuilt':True})
for x in a['false_controls']:
 n=x['module'];(Q/(n+'.lean')).write_bytes((F/(n+'.lean')).read_bytes());P.run(n,False,1);results.append({'module':n,'expected_exit':1})
old={};fresh={}
for k,b in enumerate(a['audits']):
 out=Q/('audit-'+str(k));out.mkdir();n='ReplayStored'+str(k)
 (Q/(n+'.lean')).write_text(I.source(['ProviderResumeControls'],b['producers'],out));P.run(n,False,0)
 for row in I.parse(out,b['producers'],Q):fresh[row['name']]=row
 for prod in b['producers']:
  with gzip.open(R/b['directory']/(prod+'.json.gz'),'rt') as f:
   for row in json.load(f):old[row['name']]=row
assert old.keys()==fresh.keys()
for n in old:
 for key in ['producer','index','name','kind','type','body','body_scope','axiom_references']:
  assert old[n][key]==fresh[n][key],(n,key)
n='ReplayHostile';out=Q/'hostile';out.mkdir();(Q/(n+'.lean')).write_text(I.source(['ProviderAuditGhost'],['ProviderAuditGhost'],out));P.run(n,False,1);I.parse(out,['ProviderAuditGhost'],Q,True)
rec={'status':'PASS_EXACT_SAME_LINEAGE_REPLAY','source_root':str(F.relative_to(R)),'replay_root':str(Q.relative_to(R)),'checked_modules':results,'own_source_modules_rebuilt':len(a['source_modules']),'frozen_dependencies_rebuilt':0,'stored_occurrences':len(fresh),'audit_producers':sum(len(b['producers']) for b in a['audits']),'hostile_axiom':'CAUGHT','independent_credit':0,'scope':'Source checker only; nativeIR, production dispatch and whole-solver bound remain open.'}
(Q/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');
if (D/'resume_20261016T083330Z').exists():(D/'resume_20261016T083330Z/REPLAY-RESULT-v1.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps(rec),flush=True)
