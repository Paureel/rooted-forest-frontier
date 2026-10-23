#!/usr/bin/env python3
"""Same-lineage source replay in a fresh root; zero frozen dependency rebuilds."""
from pathlib import Path
import datetime,gzip,hashlib,importlib.util,json,os,sys
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());F=R/(sys.argv[1] if len(sys.argv)>1 else (str(D.relative_to(R)) if (D/'receipt.json').exists() else json.loads((D/'FINAL-ROOT-v1.json').read_text())['root']));a=json.loads((F/'receipt.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if (F/'manifest.json').exists():
 for x in json.loads((F/'manifest.json').read_text())['immutable_files']:assert sha(R/x['path'])==x['sha256']
def load(n,p):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
P=load('caller_replay_pilot',F/'pilot.py');I=load('caller_replay_audit',F/'instrument.py');base=json.loads((F/'ROOT-v1.json').read_text());Q=R/'results'/('algorithm-universal233-binary-producer-standalone-replay-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));Q.mkdir();P.O=Q
for dep in base['dependencies']:os.symlink((F/(dep['module']+'.olean')).resolve(),Q/(dep['module']+'.olean'))
for n in a['modules']:
 (Q/(n+'.lean')).write_bytes((F/(n+'.lean')).read_bytes());P.run(n,True,0)
for f in a['false_controls']:
 n=f['module'];(Q/(n+'.lean')).write_bytes((F/(n+'.lean')).read_bytes());P.run(n,False,1)
old={};fresh={}
for k,b in enumerate(a['audits']):
 out=Q/('audit-'+str(k));out.mkdir();n='ProducerReplayAudit'+str(k);(Q/(n+'.lean')).write_text(I.source(a['modules'],b['producers'],out));P.run(n,False,0)
 for r in I.parse(out,b['producers'],Q):fresh[r['name']]=r
 for prod in b['producers']:
  with gzip.open(R/b['directory']/(prod+'.json.gz'),'rt') as f:
   for r in json.load(f):old[r['name']]=r
assert old.keys()==fresh.keys()
for n in old:
 for k in ['producer','index','name','kind','type','body','body_scope','axiom_references']:assert old[n][k]==fresh[n][k],(n,k)
for n in ['ProducerAuditGhost','ProducerBadConversion']:
 (Q/(n+'.lean')).write_bytes((F/(n+'.lean')).read_bytes());P.run(n,True,0)
for n,hostile in [('ProducerAuditGhost',True),('ProducerBadConversion',False)]:
 out=Q/n;out.mkdir();audit=n+'Audit';(Q/(audit+'.lean')).write_text(I.source([n],[n],out));P.run(audit,False,1 if hostile else 0);rs=I.parse(out,[n],Q,hostile)
 if not hostile:assert any(r['name']=='producerBadDecode' and 'GenericForest.ScalarBits.decode' in r['references'] for r in rs)
r={'status':'PASS_SAME_LINEAGE_STANDALONE_SOURCE_REPLAY','root':str(Q.relative_to(R)),'source_root':str(F.relative_to(R)),'own_source_modules_rebuilt':len(a['modules']),'frozen_dependencies_rebuilt':0,'stored_records_matched':len(fresh),'false_claims_caught':len(a['false_controls']),'axiom_control':'CAUGHT','conversion_control':'CAUGHT','independent_credit':0};(Q/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
if (D/'FINAL-ROOT-v1.json').exists():(D/'REPLAY-RESULT-v1.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r),flush=True)
