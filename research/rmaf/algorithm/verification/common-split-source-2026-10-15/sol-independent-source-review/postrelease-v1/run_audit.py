#!/usr/bin/env python3
"""Own released-producer execution driver. Every bounded operation is retained."""
import argparse, hashlib, json, os, pathlib, subprocess, time
P=pathlib.Path(__file__).resolve().parent
ROOT=next(q for q in P.parents if (q/'bootloops-python').exists())
SYS=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0'
ENV=os.environ.copy();ENV.update(LEAN_PATH=str(P/'cold'),AUDIT_SYSROOT=str(SYS))
ORDER=json.loads((P/'SOURCE-HEADER-AUDIT-v1.json').read_text())['topological_order']
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def one(m,tag,timeout):
 out=P/'producer-rows'/(m+'.jsonl');out.parent.mkdir(exist_ok=True)
 if out.exists():raise ValueError('retain original receipt, no overwrite '+m)
 cmd=[str(SYS/'bin/lean'),'--run',str(P/'ProducerAudit.lean'),str(out),m]
 start=time.perf_counter()
 try:
  z=subprocess.run(cmd,cwd=P,env=ENV,capture_output=True,text=True,timeout=timeout)
  code=z.returncode;log=z.stdout+z.stderr
 except subprocess.TimeoutExpired as e:code=124;log='TIMEOUT\n'+str(e.stdout)+str(e.stderr)
 logs=P/'audit-logs';logs.mkdir(exist_ok=True);(logs/(tag+'-'+m+'.log')).write_text(log)
 r={'module':m,'tag':tag,'code':code,'seconds':time.perf_counter()-start,'command':cmd,
    'receipt':str(out),'receipt_sha256':sha(out) if out.exists() else None,
    'bytes':out.stat().st_size if out.exists() else 0}
 if code==0:
  rows=parts=views=extra=0;maxrow=0;names=set();ax=set()
  with out.open('rb') as f:
   while line:=f.readline(32*1024*1024+1):
    if len(line)>32*1024*1024:raise ValueError('record cap exceeded')
    maxrow=max(maxrow,len(line));v=json.loads(line)
    if v['record']=='occurrence':
     rows+=1;names.add(v['stored_name']);views+=v.get('exported_view_proof') is not None
     ax.update((v.get('exported_view_proof') or v)['closure']['axioms'])
    if v['record']=='producer_part':parts+=1;extra+=len(v['compiler_extra_names'])
  r.update(stored_occurrences=rows,distinct_names=len(names),parts=parts,qualified_view_candidates=views,
    compiler_extra_names_uninspected=extra,maxrow_bytes=maxrow,effective_axiom_union=sorted(ax))
 with (P/'AUDIT-EXECUTIONS.jsonl').open('a') as f:f.write(json.dumps(r,sort_keys=True)+'\n')
 print(json.dumps(r,sort_keys=True),flush=True)
 if code:raise RuntimeError('audit failed '+m)
 return r
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--offset',type=int,default=0);a.add_argument('--limit',type=int,default=1);a.add_argument('--tag',default='pilot');v=a.parse_args()
 deadline=time.perf_counter()+50
 for m in ORDER[v.offset:v.offset+v.limit]:
  remaining=deadline-time.perf_counter()
  if remaining<2:break
  one(m,v.tag,min(50,remaining))
