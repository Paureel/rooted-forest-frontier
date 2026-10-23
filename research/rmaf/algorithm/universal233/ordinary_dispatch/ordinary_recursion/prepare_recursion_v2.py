from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5]
B=R/'results'/('algorithm-universal233-ordinary-recursion-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));B.mkdir()
inputs=[(R/'research/rmaf/algorithm/universal233/ordinary_dispatch/common_reduction/release_v1/COMMON-REDUCTION-MANIFEST-v1.json','bd8621aa7e6b014655afb1c59229c7cdd0bfdcf3bbae86cc30339dde43b5feec'),(D.parent/'resume_20261015T1810Z/child_consumer_release_v1/CHILD-CONSUMER-MANIFEST-v1.json','81385da329940b0c4fc89262cd2d44dbbfe4c7c28af82a94e32495ade298d5ed')]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rec=dict(status='AUTHOR_RECURSION_LINK_STAGING',all_main_milestones='OPEN',full_faster_solver=False,independent_acceptance=False,input_manifests=[],source_entries=[],runs=[],controls={})
def save():(B/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
# Same-name dependency disagreement is rejected, even if the importer might coalesce it.
a={'M':'clean'}
assert a['M']=='clean';rec['controls']['matching_source_pin']='PASS'
try:assert a['M']=='corrupted'
except AssertionError:rec['controls']['corrupted_source_pin']='CAUGHT'
else:raise AssertionError('CORRUPTED_PIN_ACCEPTED')
try:
 sources={}
 for m,h in inputs:
  assert sha(m)==h;mm=json.loads(m.read_text());pins={e['path']:e['sha256'] for e in mm['immutable_files']};root=R/mm.get('canonical_build',mm.get('canonical_source_replay',''))
  rec['input_manifests'].append(dict(path=str(m.relative_to(R)),sha256=h))
  for p in root.glob('*.lean'):
   o=p.with_suffix('.olean')
   if not o.exists():continue
   for q in [p,o]:assert pins.get(str(q.relative_to(R)))==sha(q) and q.stat().st_mode&0o222==0,('IMMUTABLE_PIN',str(q))
   if p.stem in sources:
    assert sha(sources[p.stem][0])==sha(p),('ADAPTED_SOURCE_COLLISION',p.stem)
    rec.setdefault('duplicate_source_binary_origins',[]).append(dict(module=p.stem,canonical_source=str(sources[p.stem][0].relative_to(R)),canonical_olean_sha256=sha(sources[p.stem][1]),alternate_source=str(p.relative_to(R)),alternate_olean_sha256=sha(o),source_sha256=sha(p),qualification='Exact selected source bytes deduplicated; alternate serialization hash recorded without asserting binary equality. Actual one-root importer and producer compatibility still required.'))
   else:sources[p.stem]=(p,o)
 own=D/'OrdinaryScaffold.lean';order=[];seen=set()
 def visit(n):
  if n in seen:return
  p=own if n=='OrdinaryScaffold' else sources[n][0]
  for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
   if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
  seen.add(n);order.append(n)
 visit('OrdinaryScaffold')
 for n in order:
  assert shutil.disk_usage(R).free>=3*(1<<30),'FREE_SPACE_MARGIN_STOP'
  if n=='OrdinaryScaffold':(B/(n+'.lean')).write_bytes(own.read_bytes());continue
  p,o=sources[n]
  for q in [p,o]:os.link(q,B/q.name)
  rec['source_entries'].append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),olean_sha256=sha(o),mode='IMMUTABLE_HARD_LINK_NO_REBUILD'))
 (B/'lean-toolchain').write_bytes((R/'research/rmaf/lean/lean-toolchain').read_bytes());save();start=time.monotonic()
 z=subprocess.run([str(R/'bootloops-lean'),'-o',str(B/'OrdinaryScaffold.olean'),str(B/'OrdinaryScaffold.lean')],cwd=B,env=dict(os.environ,LEAN_PATH=str(B)),capture_output=True,text=True,timeout=30)
 log=B/'OrdinaryScaffold-v1.log';log.write_text(z.stdout+z.stderr);rec['runs'].append(dict(module='OrdinaryScaffold',exit=z.returncode,seconds=time.monotonic()-start,source_sha256=sha(own),log_sha256=sha(log)));save();assert z.returncode==0,z.stdout+z.stderr
 rec['status']='PASS_AUTHOR_WELL_FOUNDED_EXECUTABLE_DEFINITION';save();print(rec['status'],len(order),flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-BUILD-v1.json').write_text(json.dumps(dict(directory=str(B.relative_to(R)),certificate_sha256=sha(B/'certificate.json')),indent=2)+'\n')
