# One-shot dependency adapter. Existing exact frozen canonical build covers all
# imports, so no package path union or replacement meters are introduced.
from pathlib import Path
import hashlib,json,os,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[5]
M=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/ordinary_full_source_integration_20261016T092805Z/FINAL-MANIFEST-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(M)=='1599d924619ee19eca9d20699eb7c7158f4c5fe3ef62efcf4aae0259a95a131c'
m=json.loads(M.read_text());P=R/m['canonical_build'];B=D/'build';assert not B.exists();B.mkdir()
assert shutil.disk_usage(R).free>=3*(1<<30)
files={x['path']:x for x in m['immutable_files']};seen=set();rows=[]
def add(n):
 if n in seen:return
 seen.add(n);p=P/(n+'.lean');o=P/(n+'.olean')
 for f in [p,o]:
  e=files[str(f.relative_to(R))];assert sha(f)==e['sha256'];assert not f.stat().st_mode&0o222
 for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
  if dep.split('.')[0] not in {'Lean','Std','Init'}:add(dep)
 row={'module':n}
 for kind,f in [('source',p),('object',o)]:
  stat=f.stat();row[kind]={'path':str(f.relative_to(R)),'sha256':sha(f),'mode':oct(stat.st_mode&0o777),'inode':stat.st_ino,'bytes':stat.st_size};os.link(f,B/f.name)
 rows.append(row)
for n in ['Rule4CallerSource','ChildrenSourceBound']:add(n)
shutil.copyfile(P/'lean-toolchain',B/'lean-toolchain')
(D/'DEPENDENCY-PROVENANCE-v1.json').write_text(json.dumps({'version':1,'single_canonical_context':str(P.relative_to(R)),'manifest_sha256':sha(M),'compatibility':'Identical chosen source/object pairs from one frozen context, no alternatives selected','modules':rows},indent=2)+'\n')
(D/'BUILD-v1.json').write_text(json.dumps({'directory':str(B.relative_to(R))},indent=2)+'\n')
print('EXACT_FROZEN_CONTEXT_LINKED',len(rows))
