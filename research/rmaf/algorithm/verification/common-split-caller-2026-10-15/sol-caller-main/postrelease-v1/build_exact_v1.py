import argparse,hashlib,json,os,pathlib,re,subprocess,time
P=pathlib.Path(__file__).resolve().parent;ROOT=P.parents[6]
M=ROOT/'research/rmaf/algorithm/universal233/rule5_common_split_caller/COMMON-SPLIT-CALLER-MANIFEST-v1.json'
INPUTS=ROOT/'research/rmaf/algorithm/universal233/rule5_common_split_caller/CALLER-SOURCE-INPUTS-v1.json'
LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory():
 d=json.loads(M.read_text()); rows=[]
 assert sha(M)=='3da4d51890af8e552b9942667f0f61afff9f6def6af58073f8f1d05286f1714e'
 for group in ['immutable_files','external_input_pins']:
  for r in d[group]:
   f=ROOT/r['path'];assert f.stat().st_size==r['bytes'] and sha(f)==r['sha256'],r['path'];rows.append(dict(r,group=group))
 ins=json.loads(INPUTS.read_text());members={r['path']:r for r in rows}; names={r['module'] for r in ins};assert len(names)==len(ins)
 sources=[]
 for r in ins:
  assert r['source'] in members and members[r['source']]['sha256']==r['sha256']
  f=ROOT/r['source']; text=f.read_text();imports=[]
  for line in text.splitlines():
   match=re.match(r'^\s*import\s+([A-Za-z0-9_. ]+)\s*$',line)
   if match:imports+=match[1].split()
  assert all(x in names or x in {'Std','Lean','Init'} for x in imports),(r['module'],imports)
  sources.append(dict(r,imports=imports,bytes=f.stat().st_size))
 return {'manifest_sha256':sha(M),'members':rows,'sources':sources}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['pilot','full']);a=ap.parse_args();start=time.perf_counter();d=inventory();(P/('integrity-'+a.mode+'-v1.json')).write_text(json.dumps(d,indent=2)+'\n')
 src=P/'scientific-src';b=P/'scientific-build';src.mkdir(exist_ok=True);b.mkdir(exist_ok=True)
 for r in d['sources']:
  f=src/(r['module']+'.lean')
  if f.exists():assert sha(f)==r['sha256']
  else:f.write_bytes((ROOT/r['source']).read_bytes());f.chmod(0o444)
 order=[];todo={r['module']:r for r in d['sources']}
 while todo:
  ready=[n for n,r in todo.items() if all(x in order or x not in todo for x in r['imports'])];assert ready,'cyclic imports'
  for n in ready:order.append(n);del todo[n]
 (P/'source-order-v1.json').write_text(json.dumps(order,indent=2)+'\n') if not (P/'source-order-v1.json').exists() else None
 env=dict(os.environ);env['LEAN_PATH']=str(b)
 v=subprocess.run([str(LEAN),'--version'],env=env,text=True,capture_output=True,timeout=10)
 records=[];report={'status':'FAIL','mode':a.mode,'commands':records,'toolchain':v.stdout,'lean_binary_sha256':sha(LEAN),'source_count':len(order),'script_sha256':sha(pathlib.Path(__file__))}
 try:
  if a.mode=='pilot':assert not list(b.glob('*.olean')); todo=order[:3]
  else:
   prior=json.loads((P/'build-pilot-v1.json').read_text());assert prior['status']=='PASS'
   todo=order[3:]
  for n in todo:
   assert not (b/(n+'.olean')).exists(),n
   at=time.perf_counter();cmd=[str(LEAN),'-o',str(b/(n+'.olean')),n+'.lean'];r=subprocess.run(cmd,cwd=src,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120);seconds=time.perf_counter()-at
   log='build-'+n+'-v1.log';(P/log).write_text(r.stdout);records.append({'module':n,'command':cmd,'cwd':str(src),'LEAN_PATH':str(b),'returncode':r.returncode,'seconds':seconds,'log':log});assert r.returncode==0,(n,r.stdout)
   print(json.dumps({'module':n,'seconds':seconds}),flush=True)
  inventory();report['status']='PASS'
 finally:
  report['seconds']=time.perf_counter()-start;report['compiled']=len(records);report['built_oleans']=len(list(b.glob('*.olean')));(P/('build-'+a.mode+'-v1.json')).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='commands'}))
if __name__=='__main__':main()
