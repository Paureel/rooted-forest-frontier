#!/usr/bin/env python3
"""One-shot author isolated literal module closure for the actual child binding."""
from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5]
B=R/'results/algorithm-universal233-ordinary-source-pool-20261015T144445575127Z'
L=R/'results/algorithm-universal233-forest-local-ih-replay-v2-20261015T182229550641Z'
O=R/'results'/('algorithm-universal233-ordinary-child-binding-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rec=dict(status='RUNNING_AUTHOR_DEVELOPMENT',all_main_milestones='OPEN',independent_acceptance=False,runs=[],sources=[],inputs={})
for p in [Path(__file__),D/'ChildForestBinding.lean',D/'CHILD-CONSUMER-TARGET-v1.md',B/'construction.json',L/'certificate.json']:rec['inputs'][str(p.relative_to(R))]=sha(p)
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
save()
try:
 pool=json.loads((B/'construction.json').read_text());assert all(x['exit']==0 for x in pool['runs'])
 source={e['module']:(B/(e['module']+'.lean'),e['sha256']) for e in pool['source_modules']}
 local=json.loads((L/'certificate.json').read_text());assert local['status']=='PASS_AUTHOR_SOURCE_REPLAY_PENDING_COMPRESSED_PRODUCER_AUDIT'
 for e in local['source_entries']:
  n=e['module'];p=L/(n+'.lean');assert sha(p)==e['adapted_sha256']
  if n in source:assert source[n][1]==sha(p),'LITERAL_MODULE_COLLISION|'+n
  else:source[n]=(p,sha(p))
 source['ChildForestBinding']=(D/'ChildForestBinding.lean',sha(D/'ChildForestBinding.lean'))
 order=[];seen=set();active=set()
 def visit(n):
  if n in seen:return
  assert n not in active and n in source,('IMPORT_CLOSURE',n);active.add(n)
  p,h=source[n];assert sha(p)==h
  for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
   if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
  active.remove(n);seen.add(n);order.append(n)
 visit('ChildForestBinding')
 rec['sources']=[dict(module=n,path=str(source[n][0].relative_to(R)),sha256=source[n][1]) for n in order];save()
 (O/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
 for n in order:(O/(n+'.lean')).write_bytes(source[n][0].read_bytes())
 for n in order:
  assert shutil.disk_usage(R).free>=3*(1<<30),'FREE_SPACE_MARGIN_STOP';start=time.monotonic();p=subprocess.run([str(R/'bootloops-lean'),'-o',str(O/(n+'.olean')),str(O/(n+'.lean'))],cwd=O,env=dict(os.environ,LEAN_PATH=str(O)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=30)
  (O/(n+'.log')).write_text(p.stdout);rec['runs'].append(dict(module=n,exit=p.returncode,seconds=time.monotonic()-start));save()
  if p.returncode:raise RuntimeError('FIRST_LITERAL_CONSUMER_FAILURE|'+n+'|'+p.stdout[-6000:])
  if len(rec['runs'])%20==0 or n=='ChildForestBinding':print('BUILT',len(rec['runs']),n,flush=True)
 for p,h in rec['inputs'].items():assert sha(R/p)==h
 rec.update(status='PASS_AUTHOR_CHILD_BINDING_SOURCE_BUILD',source_builds=len(order),first_external_gap='Actual ordinary step dispatch, selector case applicability/coverage and well-founded global OrdinaryIH; full source/bit/payload recurrence OPEN. Producer audit remains pending.')
 save();print(rec['status'],len(order),flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-CHILD-BINDING-v1.json').write_text(json.dumps(dict(directory=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n')
