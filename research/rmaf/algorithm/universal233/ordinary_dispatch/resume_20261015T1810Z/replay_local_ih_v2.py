#!/usr/bin/env python3
"""One-shot repaired source closure replay. Producer audit remains separate.
Keeps the failed79-module replay unchanged and does not dump proof bodies.
"""
from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5];P=D.parent/'forest_local_ih';M=R/'research/rmaf/algorithm/ordinary_dispatch/forest_min_completion'
F=R/'research/rmaf/algorithm/universal233/forest_solver/FOREST-SOLVER-MANIFEST-v3.json'
O=R/'results'/('algorithm-universal233-forest-local-ih-replay-v2-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):assert sha(p)==h,'SOURCE_PIN_MISMATCH|'+str(p)
rec=dict(status='SOURCE_CLOSURE_RUNNING',all_main_milestones='OPEN',independent_acceptance=False,full_ordinary_solver=False,runtime_claim=False,source_work_claim=False,runs=[],inputs={},source_entries=[])
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
for p in [Path(__file__),D/'COMPRESSED-AUDIT-AMENDMENT-v1.md',F,M/'FOREST-MIN-COMPLETION-MANIFEST-v1.json',M/'STACK-PINS.json',P/'LocalCongruence.lean',P/'LocalExact.lean',P/'LocalControls.lean',P/'TransferControls.lean']:
 rec['inputs'][str(p.relative_to(R))]=sha(p)
save()
try:
 pin(F,'89937a6f71bceb2dbeb64917b4b805e8f193fa485b00ec28acecdc95d047dcf5')
 pin(M/'FOREST-MIN-COMPLETION-MANIFEST-v1.json','0be74cd7bfc28cfaa382ea0610472bea7d64e601a7cab5919727ee993ca2cef4')
 forest=json.loads(F.read_text());fc=R/forest['canonical_receipt']/'certificate.json'
 fpins={e['path']:e['sha256'] for e in forest['immutable_files']};pin(fc,fpins[str(fc.relative_to(R))])
 entry=json.loads(fc.read_text())['source_inputs']+json.loads((M/'STACK-PINS.json').read_text())
 for n in ['LocalCongruence','LocalExact','LocalControls','TransferControls']:
  p=P/(n+'.lean');entry.append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),adaptations={},adapted_sha256=sha(p)))
 sources={};texts={}
 for e in entry:
  p=R/e['path'];pin(p,e['sha256']);s=p.read_text()
  for a,b in e['adaptations'].items():s=s.replace('import '+a+'\n','import '+b+'\n')
  assert hashlib.sha256(s.encode()).hexdigest()==e['adapted_sha256']
  n=e['module']
  if n in sources:assert texts[n]==s,'INCOMPATIBLE_LITERAL_MODULE|'+n
  else:sources[n]=e;texts[n]=s
 seen=set();active=set();order=[]
 def visit(n):
  if n in seen:return
  assert n not in active,'IMPORT_CYCLE';active.add(n)
  assert n in sources,'MISSING_ACTUAL_SOURCE_DEPENDENCY|'+n
  for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',texts[n],re.M):
   if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
  active.remove(n);seen.add(n);order.append(n)
 for n in ['LocalCongruence','LocalExact','LocalControls','TransferControls']:visit(n)
 assert 'ForestDisjoint' in seen and 'ForestProgramControls' in seen
 rec['source_entries']=[sources[n] for n in order];rec['closure_modules']=len(order);rec['status']='ISOLATED_SOURCE_BUILD_RUNNING';save()
 (O/'lean-toolchain').write_bytes((R/'research/rmaf/lean/lean-toolchain').read_bytes())
 for n in order:(O/(n+'.lean')).write_text(texts[n])
 def run(n,build=True,want=0):
  assert shutil.disk_usage(R).free>=3*(1<<30),'FREE_SPACE_MARGIN_STOP';start=time.monotonic()
  p=subprocess.run([str(R/'bootloops-lean')]+(['-o',str(O/(n+'.olean'))] if build else [])+[str(O/(n+'.lean'))],cwd=O,env=dict(os.environ,LEAN_PATH=str(O)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=30)
  (O/(n+'.log')).write_text(p.stdout);rec['runs'].append(dict(module=n,exit=p.returncode,seconds=time.monotonic()-start));save();assert p.returncode==want,(n,p.stdout[-5000:])
 for n in order:run(n);print('BUILT',n,flush=True)
 for n in ['FalseDiscount','FalseUnboundedTransfer']:
  (O/(n+'.lean')).write_bytes((P/(n+'.lean')).read_bytes());run(n,False,1)
 for p,h in rec['inputs'].items():pin(R/p,h)
 for e in rec['source_entries']:pin(R/e['path'],e['sha256'])
 rec.update(status='PASS_AUTHOR_SOURCE_REPLAY_PENDING_COMPRESSED_PRODUCER_AUDIT',source_builds=len(order),false_controls_rejected=2,producer_audit='PENDING; do not infer producer/AX acceptance from process exit',first_external_gap='Actual well-founded ordinary dispatcher correctness and complete paid source/bit/payload recurrence remain OPEN.')
 save();print(rec['status'],len(order),flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-LOCAL-IH-v2.json').write_text(json.dumps(dict(directory=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n')
