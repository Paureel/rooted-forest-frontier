from pathlib import Path
from hashlib import sha256
from datetime import datetime,timezone
import json,subprocess,os,time,gzip
H=Path(__file__).resolve().parent;ROOT=H.parents[5];B=H/'isolated';LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean';a=json.loads((H/'SOURCE-ADOPTION-v2.json').read_text());mods=a['order'];logs=H/'stored-consumer-producers-v4';logs.mkdir(exist_ok=True)
pilot=json.loads((H/'stored-rmaf-pilot-v2.json').read_text());plan={'writtenUTC':datetime.now(timezone.utc).isoformat(),'unchangedQualifiedDetector':True,'pilotModule':'RMAF','pilotSeconds':pilot['seconds'],'fixedModules':3,'conservativeProjectionSeconds':3*pilot['seconds']*3,'perProcessCapSeconds':60,'method':'one actual scientific producer per process; no source, detector or mathematical expectation change'};(H/'STORED-TIMING-PLAN-v4.json').write_text(json.dumps(plan,indent=2)+'\n')
previous=json.loads((H/'STORED-OCCURRENCE-INDEX-v2.json').read_text());prior_summary=json.loads((H/'STORED-AUDIT-SUMMARY-v2.json').read_text());records=prior_summary['records'].copy();all_rows=previous['occurrences'].copy();producers=previous['producers'].copy();start=time.perf_counter();standard={'propext','Classical.choice','Quot.sound'}
for n in mods[-3:]:
 probe=B/('ProbeStored_'+n+'.lean');probe.write_text('import ProducerAudit\nimport ConsumerControls\n#sol_producers "'+n+'"\n');raw=logs/(n+'.log');t=time.perf_counter()
 with raw.open('w') as out:r=subprocess.run([str(LEAN),probe.name],cwd=B,env={**os.environ,'LEAN_PATH':str(B)},stdout=out,stderr=subprocess.STDOUT,timeout=60)
 rec={'producer':n,'exit':r.returncode,'seconds':time.perf_counter()-t,'rawBytes':raw.stat().st_size};records.append(rec);assert r.returncode==0,(n,str(raw))
 rows=[];ps=[];module_names=[]
 for line in raw.read_text().splitlines():
  if line.startswith('MODULES\t'):module_names=json.loads(line[8:])
  elif line.startswith('PRODUCER\t'):ps.append(json.loads(line[9:]))
  elif line.startswith('OCCURRENCE\t'):rows.append(json.loads(line[11:]))
 assert len(ps)==1 and ps[0]['producer']==n
 assert [row['stored']['name'] for row in rows]==ps[0]['constNames']
 assert Path(ps[0]['oleanPath']).resolve()==(B/(n+'.olean')).resolve()
 assert not [m for m in module_names if m not in mods+['ProducerAudit'] and not(m in ['Init','Std','Lean'] or m.startswith(('Init.','Std.','Lean.')))],('unknown-module',n)
 for row in rows:
  assert row['producer']==n and row['stored']['kind']!='axiom',('direct-custom-axiom',n,row['stored']['name'])
  assert all(ref['resolvedKind']!='MISSING' and set(ref['resolvedAxioms'])<=standard for ref in row['references']),('invalid-reference',n,row['stored']['name'])
  for key in ['stored','resolved']:
   if row[key] is not None:
    for field in ['typeExpr','valueExpr']:
     v=row[key].pop(field)
     row[key][field+'SHA256']=None if v is None else sha256(v.encode()).hexdigest()
  row['literalTypeBodyEvidence']=str((logs/(n+'.log.gz')).relative_to(H))
 with raw.open('rb') as src,gzip.open(logs/(n+'.log.gz'),'wb',compresslevel=6) as dest:
  for block in iter(lambda:src.read(1048576),b''):dest.write(block)
 raw.unlink();producers.extend(ps);all_rows.extend(rows);rec['occurrences']=len(rows);print(json.dumps(rec),flush=True)
assert len(set((r['producer'],r['occurrenceIndex']) for r in all_rows))==len(all_rows)
names={r['stored']['name'] for r in all_rows};dup={n:[r['producer'] for r in all_rows if r['stored']['name']==n] for n in names};dup={n:v for n,v in dup.items() if len(v)>1}
summary={'status':'STORED-PRODUCER-AUDIT-PASS','scientificProducers':len(mods),'storedOccurrences':len(all_rows),'uniqueNames':len(names),'coalescedOccurrencesBeyondNames':len(all_rows)-len(names),'duplicateNameProducers':dup,'privateOccurrences':sum(r['stored']['name'].startswith('_private.') for r in all_rows),'directCustomAxioms':[],'permittedResolvedReferenceAxioms':sorted(standard),'producerAndResolvedOriginSeparatelyRecorded':True,'actualKindTypeBodyRecorded':True,'exactTypeBodyRepresentation':'full reprStr bytes in per-producer gzip; SHA256 adapters in occurrence index','noScientificOleansCopied':True,'records':records,'seconds':prior_summary['seconds']+time.perf_counter()-start,'scope':'Every stored occurrence in exact66 scientific producer arrays; post-import lazy realizations audited separately; no all-possible synthesized-equation completeness.'}
(H/'STORED-OCCURRENCE-INDEX-v4.json').write_text(json.dumps({'producers':producers,'occurrences':all_rows},indent=2)+'\n');(H/'STORED-AUDIT-SUMMARY-v4.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k not in ['records','duplicateNameProducers']}))
