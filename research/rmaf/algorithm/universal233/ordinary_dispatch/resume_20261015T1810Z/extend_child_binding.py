"""One-shot author same-root extension; preserves every prior file/receipt."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/'results/algorithm-universal233-ordinary-child-binding-20261015T182851721674Z';P=R/'results/algorithm-universal233-ordinary-source-pool-20261015T144445575127Z'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
source={e['module']:(P/(e['module']+'.lean'),e['sha256']) for e in json.loads((P/'construction.json').read_text())['source_modules']}
for e in json.loads((B/'certificate.json').read_text())['sources']:source[e['module']]=(R/e['path'],e['sha256'])
own=['ChildForestBinding','PaidChildren','ChildConsumerControls','CherryDispatch','Rule4Dispatch']
for n in own:source[n]=(D/(n+'.lean'),sha(D/(n+'.lean')))
order=[];seen=set();active=set()
def visit(n):
 if n in seen:return
 assert n in source and n not in active,('SOURCE_CLOSURE',n);active.add(n);p,h=source[n];assert sha(p)==h
 for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
  if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
 active.remove(n);seen.add(n);order.append(n)
for n in own:visit(n)
rec=dict(status='RUNNING_AUTHOR_EXTENSION',all_main_milestones='OPEN',independent_acceptance=False,source_entries=[dict(module=n,path=str(source[n][0].relative_to(R)),sha256=source[n][1]) for n in order],runs=[],base_receipt_sha256=sha(B/'certificate.json'))
def save():(B/'integration-extension-v1.json').write_text(json.dumps(rec,indent=2)+'\n')
save()
try:
 for n in order:
  p,h=source[n];q=B/(n+'.lean')
  if q.exists():assert sha(q)==h,('EXISTING_SELECTED_SOURCE_CHANGED',n)
  else:q.write_bytes(p.read_bytes())
  if n in own or not (B/(n+'.olean')).exists():
   assert shutil.disk_usage(R).free>=3*(1<<30),'FREE_SPACE_MARGIN_STOP';start=time.monotonic()
   z=subprocess.run([str(R/'bootloops-lean'),'-o',str(B/(n+'.olean')),str(q)],cwd=B,env=dict(os.environ,LEAN_PATH=str(B)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=30)
   log=B/(n+'-extension-v1.log');log.write_text(z.stdout);rec['runs'].append(dict(module=n,exit=z.returncode,seconds=time.monotonic()-start,log_sha256=sha(log)));save()
   assert z.returncode==0,(n,z.stdout[-7000:]);print('BUILT',n,flush=True)
 for e in rec['source_entries']:assert sha(R/e['path'])==e['sha256']
 rec.update(status='PASS_AUTHOR_INTEGRATED_CHILD_SOURCE_BUILD',source_modules=len(order),stored_producer_audit='PENDING',full_ordinary_solver=False,source_bit_payload_runtime='OPEN');save();print(rec['status'],len(order),flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
