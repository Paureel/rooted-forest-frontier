# One-shot numeric-invariant seed: the toolkit has no Lean numeric-invariant prover;
# reuse the completed source-integration import pool without rebuilding or merging.
from pathlib import Path
import hashlib,json,re,shutil,stat
D=Path(__file__).resolve().parent;R=D.parents[5]
M=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/ordinary_full_source_integration_20261016T092805Z/FINAL-MANIFEST-v1.json'
assert hashlib.sha256(M.read_bytes()).hexdigest()=='1599d924619ee19eca9d20699eb7c7158f4c5fe3ef62efcf4aae0259a95a131c'
m=json.loads(M.read_text());B=R/m['canonical_build']; pins={e['path']:e for e in m['immutable_files']}
order=[];seen=set();rows=[]
def visit(n):
 if n in seen:return
 p=B/(n+'.lean');o=B/(n+'.olean');assert p.exists() and o.exists(),n
 for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
  if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
 seen.add(n);order.append(n)
 for f in [p,o]:
  rel=str(f.relative_to(R));h=hashlib.sha256(f.read_bytes()).hexdigest();assert h==pins[rel]['sha256'],rel
  s=f.stat();rows.append(dict(path=rel,sha256=h,bytes=s.st_size,mode=stat.S_IMODE(s.st_mode),inode=s.st_ino,device=s.st_dev))
for n in ['OrdinaryStepBounds','FreshEnvelope','ReturnedPayload','ClassifierPayload','ELGeometry','MaterialBounds']:visit(n)
(D/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
(D/'DEPENDENCY-PINS-v2.json').write_text(json.dumps(dict(manifest=str(M.relative_to(R)),sha256=hashlib.sha256(M.read_bytes()).hexdigest(),pool=str(B.relative_to(R)),roots=['OrdinaryStepBounds','FreshEnvelope','ReturnedPayload','ClassifierPayload','ELGeometry','MaterialBounds'],modules=order,files=rows,no_rebuilds=True,no_pool_merge=True),indent=2)+'\n')
print('PINNED',len(order),'modules',len(rows),'files; free GiB',round(shutil.disk_usage(D).free/(1<<30),2))
