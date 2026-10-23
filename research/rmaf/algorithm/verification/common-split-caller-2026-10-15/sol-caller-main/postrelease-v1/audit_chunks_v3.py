import argparse,hashlib,importlib.util,json,os,pathlib,subprocess,time
P=pathlib.Path(__file__).resolve().parent;PRE=P.parent
s=importlib.util.spec_from_file_location('ownaudit2',P/'audit_exact_v2.py');a=importlib.util.module_from_spec(s);s.loader.exec_module(a)
D=P/'CallerProducerAudit_chunk_v3.lean'
def run(imports,producers,build,label,records):
 env=dict(os.environ);env['LEAN_PATH']=str(build);cmd=[str(a.LEAN),'--run',str(D)]+imports+['--producers']+producers;at=time.perf_counter()
 try:r=subprocess.run(cmd,cwd=P,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
 except subprocess.TimeoutExpired as e:
  (P/(label+'.log')).write_bytes(e.stdout or b'');records.append({'command':cmd,'timeout':120,'seconds':time.perf_counter()-at});raise
 (P/(label+'.log')).write_text(r.stdout);records.append({'command':cmd,'seconds':time.perf_counter()-at,'returncode':r.returncode,'LEAN_PATH':str(build)});assert r.returncode==0,r.stdout[:1000]
 d=a.g.enrich(json.loads(r.stdout));(P/(label+'.json')).write_text(json.dumps(d,indent=2)+'\n');return d
ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['controls','pilot','full']);x=ap.parse_args();records=[];at=time.perf_counter();report={'status':'FAIL','mode':x.mode,'commands':records,'detector_sha256':a.sha(D),'script_sha256':a.sha(pathlib.Path(__file__)),'replication_credit':0}
try:
 if x.mode=='controls':
  b=PRE/'origin/build-full-v2';ms=['CallerCleanA','CallerCleanB'];full=run(ms,ms,b,'chunk-v3-control-full',records);part=run(ms,['CallerCleanA'],b,'chunk-v3-control-part',records)
  assert a.g.fingerprint(part)==a.g.fingerprint(dict(full,rows=[r for r in full['rows'] if r['producer']=='CallerCleanA']))
  a.g.gate(full,ms);a.compatibility(full)
  b=PRE/'origin/private-imports';ms=['CallerPrivateClean','CallerPrivateHostile'];d=run(ms,['CallerPrivateHostile'],b,'chunk-v3-control-private',records)
  try:a.g.gate(d,['CallerPrivateHostile'])
  except ValueError as e:report['hostile_reject']=str(e)
  else:raise AssertionError('private-unused-coalesced survived')
  report['controls']=3
 else:
  assert json.loads((P/'audit-chunks-controls-v3.json').read_text())['status']=='PASS'
  ms=json.loads((P/'source-order-v1.json').read_text());b=P/'scientific-build';chunks=[ms[i:i+10] for i in range(0,len(ms),10)]
  if x.mode=='pilot':todo=[(0,chunks[0])]
  else:
   assert json.loads((P/'audit-chunks-pilot-v3.json').read_text())['status']=='PASS';todo=list(enumerate(chunks))[1:]
  for i,ns in todo:
   assert time.perf_counter()-at<1200
   d=run(ms,ns,b,'producer-chunk-v3-'+str(i),records);assert {h['module'] for h in d['producers']}==set(ns);print(json.dumps({'batch':i,'producers':len(ns),'rows':len(d['rows']),'seconds':records[-1]['seconds']}),flush=True)
  if x.mode=='full':
   ds=[json.loads((P/('producer-chunk-v3-'+str(i)+'.json')).read_text()) for i in range(len(chunks))];d=dict(ds[0],rows=sum([v['rows'] for v in ds],[]),producers=sum([v['producers'] for v in ds],[]));assert all(v['loaded_modules']==d['loaded_modules'] for v in ds)
   inv=json.loads((P/'integrity-pilot-v1.json').read_text());by={r['module']:r for r in inv['sources']};a.g.gate(d,ms,{n:['Init','Init']+by[n]['imports'] for n in ms});pd=a.compatibility(d)
   report.update({'producers':len(d['producers']),'stored':len(d['rows']),'unique_names':len({r['name'] for r in d['rows']}),'axiom_union':sorted({v for r in d['rows'] for v in r['axioms']}),'proof_body_differences':pd,'unsafe_occurrences':[[r['producer'],r['name']] for r in d['rows'] if r['unsafe']],'partial_occurrences':[[r['producer'],r['name']] for r in d['rows'] if r['partial']],'empty_producers':[r['module'] for r in d['producers'] if r['count']==0]})
   (P/'producer-combined-v3.json').write_text(json.dumps(d,indent=2)+'\n')
 report['status']='PASS'
except Exception as e:report['error']=repr(e);raise
finally:report['seconds']=time.perf_counter()-at;(P/('audit-chunks-'+x.mode+'-v3.json')).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ['commands','proof_body_differences','partial_occurrences']}))
