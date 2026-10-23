#!/usr/bin/env python3
"""Execute exact pinned fixed-instance adapter; preserve every failed attempt."""
import argparse,hashlib,json,os,pathlib,subprocess,time
P=pathlib.Path(__file__).resolve().parent
ROOT=next(q for q in P.parents if (q/'bootloops-python').exists());SYS=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0'
ENV=os.environ.copy();ENV.update(LEAN_PATH=str(P/'actual-controls')+':'+str(P/'cold'),AUDIT_SYSROOT=str(SYS))
REG=json.loads((P/'ACTUAL-CONTROL-REGISTRY-v1.json').read_text())
def normal(f):return tuple(sorted(tuple(sorted(b)) for b in f))
def family(fs):return sorted(set(normal(f) for f in fs))
def normtree(t):
 if isinstance(t,int):return str(t)
 return '('+','.join(sorted(normtree(x) for x in t))+')'
def one(r,tag,timeout):
 m=r['module'];src=P/'actual-controls'/(m+'.lean');assert hashlib.sha256(src.read_bytes()).hexdigest()==r['source_sha256']
 dest=P/'control-results'/tag;dest.mkdir(parents=True,exist_ok=True)
 if (dest/(m+'.json')).exists():raise ValueError('retain original attempt')
 start=time.perf_counter();cmd=[str(SYS/'bin/lean'),'-Ddebug.skipKernelTC=false','-o',str(src.with_suffix('.olean')),str(src)]
 z=subprocess.run(cmd,env=ENV,cwd=P,capture_output=True,text=True,timeout=timeout)
 (dest/(m+'.compile.log')).write_text(z.stdout+z.stderr)
 result={'module':m,'case_id':r['case_id'],'tag':tag,'compile_code':z.returncode,'checks':{},'issues':[],'compile_command':cmd}
 if z.returncode:result['issues'].append('actual fixture theorem compilation failed')
 else:
  cmd=[str(SYS/'bin/lean'),'-Ddebug.skipKernelTC=false','--run',str(src)]
  z=subprocess.run(cmd,env=ENV,cwd=P,capture_output=True,text=True,timeout=max(1,timeout-(time.perf_counter()-start)))
  (dest/(m+'.stdout')).write_text(z.stdout);(dest/(m+'.stderr')).write_text(z.stderr)
  result.update(run_code=z.returncode,run_command=cmd)
  if z.returncode:result['issues'].append('actual readout failed')
  else:
   actual=json.loads(z.stdout);expected=r['expected'];checks=result['checks']
   checks['id']=actual['id']==r['case_id'];checks['marked_trees']=all(normtree(a)==normtree(e) for a,e in zip(actual['marked'],expected['marked_trees']))
   checks['identity_value']=actual['identity_value']==expected['identity_rhs']
   computed=[];mins=[];allcounts=[]
   for i,pair in enumerate(actual['pairs']):
    fs=family(pair['all_af_encodings']);cost=min(len(f)-1 for f in fs);mf=[f for f in fs if len(f)-1==cost]
    computed.append(cost);mins.append(mf);allcounts.append(len(fs))
    checks['pair'+str(i)+'_proper']=pair['proper'] is True
    checks['pair'+str(i)+'_pretest_cost']=pair['pretest']['cost']==expected['costs'][i]
    checks['pair'+str(i)+'_pretest_witness']=pair['pretest']['agreement'] is True
    checks['pair'+str(i)+'_all_minima']=mf==family(expected['minima'][i])
   checks['all_costs']=computed==expected['costs'];checks['global_all_af_count']=allcounts[0]==expected['all_af_count']
   # The actual restriction readouts equal the trees used by the actual finite pair controls.
   checks['literal_restrictions']=all(normtree(actual['restrictions'][i])==normtree(actual['pairs'][1+i//2]['T' if i%2==0 else 'S']) for i in range(4))
   checks['marked_minimum_counts']=[len(mins[3]),len(mins[4])]==expected['marked_minimum_counts']
   singleton_counts=[sum((marker,) in f for f in mins[j]) for j,marker in zip([3,4],expected['markers'])]
   checks['marker_singleton_minimum_counts']=singleton_counts==expected['marker_singleton_minimum_counts']
   result.update(actual_costs=computed,actual_minimum_counts=[len(f) for f in mins],actual_af_counts=allcounts,actual_marker_singleton_minimum_counts=singleton_counts)
   result['issues'] += [k for k,v in checks.items() if not v]
 result.update(seconds=time.perf_counter()-start,status='MISMATCH' if result['issues'] else 'PASS_FIXED_OLD_CONTROL')
 (dest/(m+'.json')).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 with (P/'ACTUAL-CONTROL-EXECUTIONS.jsonl').open('a') as f:f.write(json.dumps(result,sort_keys=True)+'\n')
 print(json.dumps({k:result[k] for k in ['module','case_id','status','seconds','issues']},sort_keys=True),flush=True)
 if result['issues']:raise RuntimeError('actual control failed; preserve before repair')
 return result
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--offset',type=int,default=0);a.add_argument('--limit',type=int,default=1);a.add_argument('--tag',default='pilot');v=a.parse_args();deadline=time.perf_counter()+50
 for r in REG[v.offset:v.offset+v.limit]:
  rem=deadline-time.perf_counter()
  if rem<2:break
  one(r,v.tag,min(50,rem))
