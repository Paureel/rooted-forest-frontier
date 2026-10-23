#!/usr/bin/env python3
"""Own bounded cold-source compiler driver; released scientific source only."""
import argparse,hashlib,json,os,pathlib,subprocess,time
P=pathlib.Path(__file__).resolve().parent
ROOT=next(q for q in P.parents if (q/'bootloops-python').exists())
SYS=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0';LEAN=SYS/'bin/lean'
ENV=os.environ.copy();ENV['LEAN_PATH']=str(P/'cold');ENV['LEAN_SRC_PATH']=str(P/'cold')+':'+str(SYS/'src/lean');ENV['AUDIT_SYSROOT']=str(SYS)
REG={r['module']:r for r in json.loads((P/'COLD-SOURCE-REGISTRY-v1.json').read_text())};ORDER=json.loads((P/'SOURCE-HEADER-AUDIT-v1.json').read_text())['topological_order']

def compile_one(name,tag):
 r=REG[name];src=pathlib.Path(r['source']);assert hashlib.sha256(src.read_bytes()).hexdigest()==r['source_sha256'];out=pathlib.Path(r['olean'])
 if out.exists():raise ValueError('existing scientific binary forbidden for cold compilation '+name)
 cmd=[str(LEAN),'-Ddebug.skipKernelTC=false','-o',str(out),str(src)];start=time.perf_counter()
 try:
  z=subprocess.run(cmd,cwd=P/'cold',env=ENV,text=True,capture_output=True,timeout=50);code=z.returncode;log=z.stdout+z.stderr
 except subprocess.TimeoutExpired as e:code=124;log='TIMEOUT50s\n'+str(e.stdout)+str(e.stderr)
 logpath=P/'build-logs'/(tag+'-'+name+'.log');logpath.parent.mkdir(exist_ok=True);logpath.write_text(log)
 record={'module':name,'tag':tag,'code':code,'seconds':time.perf_counter()-start,'source_sha256':r['source_sha256'],'olean_sha256':hashlib.sha256(out.read_bytes()).hexdigest() if out.exists() else None,'command':cmd,'log':str(logpath.relative_to(P)),'kernel_skip_option':False,'scientific_olean_copied':False}
 with (P/'BUILD-RESULTS.jsonl').open('a') as f:f.write(json.dumps(record,sort_keys=True)+'\n')
 print(json.dumps({k:record[k] for k in ('module','tag','code','seconds')},sort_keys=True),flush=True)
 if code:raise RuntimeError('cold build failed '+name)
 return record
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--offset',type=int,default=0);a.add_argument('--limit',type=int,default=5);a.add_argument('--tag',default='pilot');v=a.parse_args()
 for name in ORDER[v.offset:v.offset+v.limit]:compile_one(name,v.tag)
