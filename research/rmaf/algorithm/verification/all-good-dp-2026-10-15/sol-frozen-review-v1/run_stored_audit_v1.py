from pathlib import Path
from hashlib import sha256
import json,subprocess,os,time,shutil
H=Path(__file__).resolve().parent;ROOT=H.parents[5];B=H/'isolated';LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
a=json.loads((H/'SOURCE-ADOPTION-v1.json').read_text());mods=a['order'];controls=H/'producer-controls-v1';frozen=json.loads((controls/'CONTROL-MANIFEST-v1.json').read_text());e=next(r for r in frozen['files'] if r['path']=='ProducerAudit.lean');assert sha256((controls/'ProducerAudit.lean').read_bytes()).hexdigest()==e['sha256'];shutil.copyfile(controls/'ProducerAudit.lean',B/'ProducerAudit.lean')
(B/'ProbeStored.lean').write_text('import ProducerAudit\nimport ExactMinimum\n#sol_producers "'+','.join(mods)+'"\n')
records=[];start=time.perf_counter()
for label,cmd in [('compile-producer-audit',['-o','ProducerAudit.olean','ProducerAudit.lean']),('stored-occurrences',['ProbeStored.lean'])]:
 t=time.perf_counter();p=H/(label+'-v1.log')
 with p.open('w') as out:r=subprocess.run([str(LEAN),*cmd],cwd=B,env={**os.environ,'LEAN_PATH':str(B)},stdout=out,stderr=subprocess.STDOUT,timeout=60)
 records.append({'label':label,'seconds':time.perf_counter()-t,'exit':r.returncode});assert r.returncode==0,(label,str(p))
data={'modules':[],'producers':[],'occurrences':[]}
for line in (H/'stored-occurrences-v1.log').read_text().splitlines():
 for pref,key in [('MODULES\t','modules'),('PRODUCER\t','producers'),('OCCURRENCE\t','occurrences')]:
  if line.startswith(pref):
   v=json.loads(line[len(pref):]);data[key]=v if key=='modules' else data[key]+[v]
assert sorted(p['producer'] for p in data['producers'])==sorted(mods)
assert not [m for m in data['modules'] if m not in mods+['ProducerAudit'] and not(m in ['Init','Std','Lean'] or m.startswith(('Init.','Std.','Lean.')))],'unknown imported module'
for p in data['producers']:
 rows=[r for r in data['occurrences'] if r['producer']==p['producer']];assert [r['stored']['name'] for r in rows]==p['constNames'];assert Path(p['oleanPath']).resolve()==(B/(p['producer']+'.olean')).resolve()
 for r in rows:
  assert r['stored']['kind']!='axiom',('direct-custom-axiom',r['producer'],r['stored']['name'])
  assert all(ref['resolvedKind']!='MISSING' for ref in r['references']),('missing-reference',r['stored']['name'])
  assert all(set(ref['resolvedAxioms'])<={'propext','Classical.choice','Quot.sound'} for ref in r['references']),('custom-reference-axioms',r['stored']['name'])
assert len(set((r['producer'],r['occurrenceIndex']) for r in data['occurrences']))==len(data['occurrences'])
names={r['stored']['name'] for r in data['occurrences']};dup={n:[r['producer'] for r in data['occurrences'] if r['stored']['name']==n] for n in names};dup={n:v for n,v in dup.items() if len(v)>1}
summary={'status':'STORED-PRODUCER-AUDIT-PASS','scientificProducers':len(mods),'storedOccurrences':len(data['occurrences']),'uniqueNames':len(names),'coalescedOccurrencesBeyondNames':len(data['occurrences'])-len(names),'duplicateNameProducers':dup,'privateOccurrences':sum(r['stored']['name'].startswith('_private.') for r in data['occurrences']),'directCustomAxioms':[],'permittedResolvedReferenceAxioms':['propext','Classical.choice','Quot.sound'],'producerAndResolvedOriginSeparatelyRecorded':True,'actualKindTypeBodyRecorded':True,'noScientificOleansCopied':True,'processes':records,'seconds':time.perf_counter()-start,'qualification':str((controls/'CONTROL-MANIFEST-v1.json').relative_to(H)),'scope':'All stored occurrences in exact63-producer imported arrays; post-import generated realizations separately audited. Reference closures use resolved Lean APIs and do not replace direct occurrence inspection.'}
(H/'STORED-OCCURRENCES-v1.json').write_text(json.dumps(data,indent=2)+'\n');(H/'STORED-AUDIT-SUMMARY-v1.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
