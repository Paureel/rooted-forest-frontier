import argparse,collections,hashlib,importlib.util,json,os,pathlib,subprocess,time
P=pathlib.Path(__file__).resolve().parent;PRE=P.parent;ROOT=P.parents[6];LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean';DETECT=PRE/'origin/CallerProducerAudit_v2.lean'
spec=importlib.util.spec_from_file_location('owncallerorigin',PRE/'origin_gate_v2.py');g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(args,cwd,build,label,records):
 env=dict(os.environ);env['LEAN_PATH']=str(build);at=time.perf_counter();r=subprocess.run([str(LEAN)]+args,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120);log=label+'.log';(P/log).write_text(r.stdout);records.append({'command':[str(LEAN)]+args,'cwd':str(cwd),'LEAN_PATH':str(build),'seconds':time.perf_counter()-at,'returncode':r.returncode,'log':log});assert r.returncode==0,(label,r.stdout[:1000]);return r.stdout
def audit(ms,build,label,records):
 d=g.enrich(json.loads(run(['--run',str(DETECT)]+ms,P,build,label,records)));(P/(label+'.json')).write_text(json.dumps(d,indent=2)+'\n');return d
def compatibility(d):
 conflicts=[];proofdiff=[]
 for r in d['rows']:
  if r['kind']!=r['resolved_kind'] or r['type']!=r['resolved_type']:conflicts.append([r['producer'],r['name'],'kind/type'])
  if r['body']!=r['resolved_body'] or r['recursor_rules']!=r['resolved_recursor_rules']:
   if r['kind']=='theorem' and r['resolved_kind']=='theorem' and r['type']==r['resolved_type']:proofdiff.append([r['producer'],r['name']])
   else:conflicts.append([r['producer'],r['name'],'nonproof body/rules'])
 if conflicts:raise ValueError('incompatible producer/resolved values '+repr(conflicts))
 return proofdiff
def main():
 ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['controls','pilot','full']);a=ap.parse_args();records=[];at=time.perf_counter();report={'status':'FAIL','mode':a.mode,'commands':records,'script_sha256':sha(pathlib.Path(__file__)),'detector_sha256':sha(DETECT),'own_gate_sha256':sha(PRE/'origin_gate_v2.py'),'replication_credit':0}
 try:
  if a.mode=='controls':
   src=P/'value-controls-src';src.mkdir(exist_ok=True);b=P/'value-controls-build';b.mkdir(exist_ok=True);pins={}
   for n,v in [('CallerValueA',7),('CallerValueB',7),('CallerValueHostile',8)]:
    f=src/(n+'.lean');f.write_text('import Std\nnamespace CallerValue\ndef shared : Nat := '+str(v)+'\nend CallerValue\n');pins[n]=sha(f)
   (P/'VALUE-CONTROL-PINS-v1.json').write_text(json.dumps(pins,indent=2)+'\n')
   for n in pins:run(['-o',str(b/(n+'.olean')),n+'.lean'],src,b,'value-compile-'+n,records)
   results=[]
   for ms in [['CallerValueA','CallerValueB'],['CallerValueA','CallerValueHostile'],['CallerValueHostile','CallerValueA']]:
    d=audit(ms,b,'value-audit-'+'+'.join(ms),records);g.gate(d,ms)
    try:compatibility(d)
    except ValueError as e:
     assert 'Hostile' in ''.join(ms);results.append({'modules':ms,'rejected':True,'reason':str(e)})
    else:assert 'Hostile' not in ''.join(ms);results.append({'modules':ms,'pass':True})
   assert all(sha(src/(n+'.lean'))==h for n,h in pins.items());report['controls']=results
  else:
   assert json.loads((P/'audit-controls-v2.json').read_text())['status']=='PASS'
   ms=json.loads((P/'source-order-v1.json').read_text());ms=ms[:3] if a.mode=='pilot' else ms
   if a.mode=='full':assert json.loads((P/'audit-pilot-v1.json').read_text())['status']=='PASS'
   b=P/'scientific-build';d=audit(ms,b,'producer-'+a.mode+'-v1',records)
   inv=json.loads((P/'integrity-pilot-v1.json').read_text());by={r['module']:r for r in inv['sources']};expected={n:['Init','Init']+by[n]['imports'] for n in ms}
   g.gate(d,ms,expected);pd=compatibility(d)
   report.update({'stored':len(d['rows']),'unique_names':len({r['name'] for r in d['rows']}),'producers':len(d['producers']),'empty_producers':[r['module'] for r in d['producers'] if r['count']==0],'axiom_union':sorted({x for r in d['rows'] for x in r['axioms']}),'proof_body_differences':pd,'unsafe_occurrences':[[r['producer'],r['name']] for r in d['rows'] if r['unsafe']],'partial_occurrences':[[r['producer'],r['name']] for r in d['rows'] if r['partial']],'kind_counts':dict(collections.Counter(r['kind'] for r in d['rows']))})
  report['status']='PASS'
 except Exception as e:report['error']=repr(e);raise
 finally:report['seconds']=time.perf_counter()-at;(P/('audit-'+a.mode+'-v1.json')).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ['commands','proof_body_differences']}))
if __name__=='__main__':main()
