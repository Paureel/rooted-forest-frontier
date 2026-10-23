#!/usr/bin/env python3
"""One-shot actual candidate audit runner; uses frozen planted-tested comparison logic."""
import argparse,collections,json,os,pathlib,subprocess,sys,time
HERE=pathlib.Path(__file__).resolve().parent; ROOT=HERE.parents[5]; B=HERE/'isolated'; LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
sys.path.insert(0,str(HERE.parent/'sol-frozen-ready-v1'/'preparation'))
from audit_controls_v5 import rows_from,reject_custom_axioms
p=argparse.ArgumentParser();p.add_argument('--pilot',action='store_true');a=p.parse_args(); logs=HERE/'audit-logs';logs.mkdir(exist_ok=True); processes=[]; start=time.perf_counter()
def run(label,args):
 t=time.perf_counter();r=subprocess.run([str(LEAN),*args],cwd=B,env={**os.environ,'LEAN_PATH':str(B)},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=60)
 (logs/(label+'.log')).write_text(r.stdout);processes.append({'label':label,'exit':r.returncode,'seconds':time.perf_counter()-t});assert r.returncode==0,r.stdout
 return r.stdout
if a.pilot: run('compile-SolAudit',['-o','SolAudit.olean','SolAudit.lean'])
out=run('pilot' if a.pilot else 'full',['ProbeAuditPilot.lean' if a.pilot else 'ProbeAuditFull.lean']); tags=['pilot'] if a.pilot else ['before','after']; expected={r['module'] for r in json.loads((HERE/'release-integrity-v1.json').read_text())['formalModules']}; result={}
for tag in tags:
 rows=rows_from(out,tag); assert rows; assert len(rows)==len({r['name'] for r in rows}); counts=collections.Counter(r['origin'] for r in rows);assert set(counts)==expected,(tag,counts)
 reject_custom_axioms(rows)
 paths={}
 for line in out.splitlines():
  if line.startswith('MODULE\t'+tag+'\t'):
   _,_,m,path=line.split('\t');assert m not in paths;paths[m]=path;assert pathlib.Path(path)==B/(m+'.olean')
 assert set(paths)==expected
 result[tag]={'count':len(rows),'originCounts':dict(sorted(counts.items())),'rows':rows,'resolvedModulePaths':paths}
if not a.pilot:
 before={r['name']:r for r in result['before']['rows']}; after={r['name']:r for r in result['after']['rows']}; assert set(before)<=set(after)
 for n,r in after.items():
  if r['originAdapter']!='direct':
   producer=r['originAdapter'].split(':',1)[1];assert producer in before,(n,producer);assert before[producer]['origin']==r['origin'];assert r['rawOrigin']=='ProbeAuditFull'
  else: assert r['rawOrigin']==r['origin']
 result['forcedProducerCount']=int(next(l for l in out.splitlines() if l.startswith('FORCED\t')).split('\t')[1]);result['newGeneratedNames']=sorted(set(after)-set(before))
result.update({'status':'AUDIT-PILOT-PASS' if a.pilot else 'EXACT-SOURCE-AUDIT-PASS','processes':processes,'seconds':time.perf_counter()-start,'allowAxioms':['propext','Classical.choice','Quot.sound']})
(HERE/('audit-pilot-v1.json' if a.pilot else 'audit-full-v1.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'counts':{tag:result[tag]['count'] for tag in tags},'seconds':result['seconds']}))
