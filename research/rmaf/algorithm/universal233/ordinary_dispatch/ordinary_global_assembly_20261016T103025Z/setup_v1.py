# One-shot exact-context adapter: start from sealed hard2-front and add only
# Rule4's sealed logical modules; overlapping source/object pairs must match.
from pathlib import Path
import hashlib,json,os,re,shutil,stat
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
t=json.loads((R/'research/rmaf/monitoring/next-20261016T103025Z/GLOBAL-COST-ASSEMBLY-TARGET-v1.json').read_text());ms={}
for n in ['hard2_front','rule4_bound']:
 e=t['allowed_packages'][n];p=R/e['manifest'];assert sha(p)==e['sha256'];ms[n]=json.loads(p.read_text())
P=R/ms['hard2_front']['canonical_build'];S=R/ms['rule4_bound']['canonical_build'];B=D/'build';assert not B.exists();assert shutil.disk_usage(R).free>=3*(1<<30);B.mkdir()
files={x['path']:x for m in ms.values() for x in m.get('immutable_files',m.get('immutable_owned_files',[]))}
r4deps=json.loads((R/ms['rule4_bound']['dependency_provenance']).read_text())['modules'];r4map={x['module']:x for x in r4deps}
seen={};visited=set();rec={'version':1,'status':'CHECKING','inputs':{n:t['allowed_packages'][n] for n in ms},'modules':[],'overlap_pairs_verified':0,'object_differences':[]}
def save():(D/'DEPENDENCY-PROVENANCE-v1.json').write_text(json.dumps(rec,indent=2)+'\n')
save()
def add(n,root,package):
 key=(n,str(root))
 if key in visited:return
 visited.add(key);p=root/(n+'.lean');o=root/(n+'.olean');assert p.exists() and o.exists(),(n,root)
 for kind,f in [('source',p),('object',o)]:
  e=files.get(str(f.relative_to(R)))
  expected=e['sha256'] if e else r4map[n][kind]['sha256']
  assert sha(f)==expected and not f.stat().st_mode&0o222,(n,kind)
 for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
  if dep.split('.')[0] not in {'Init','Std','Lean'}:add(dep,root,package)
 e={'module':n,'package':package}
 for k,f in [('source',p),('object',o)]:
  z=f.stat();e[k]={'path':str(f.relative_to(R)),'sha256':sha(f),'mode':oct(stat.S_IMODE(z.st_mode)),'inode':z.st_ino,'bytes':z.st_size}
 if n in seen:
  old=seen[n];assert e['source']['sha256']==old['source']['sha256'],('SOURCE_DIFFERENCE',n)
  assert e['object']['sha256']==old['object']['sha256'],('OBJECT_DIFFERENCE_REQUIRES_ORIGINAL_CONTEXT_COMPATIBILITY',n)
  rec['overlap_pairs_verified']+=1;return
 for f in [p,o]:os.link(f,B/f.name)
 seen[n]=e;rec['modules'].append(e)
add('Hard2FrontTreeSource',P,'hard2_front');add('Rule4BoundInterface',S,'rule4_bound')
shutil.copyfile(P/'lean-toolchain',B/'lean-toolchain');rec['status']='PASS_EXACT_IDENTICAL_OVERLAPPING_SOURCE_OBJECT_CONTEXT';save();(D/'BUILD-v1.json').write_text(json.dumps({'directory':str(B.relative_to(R))},indent=2)+'\n');print(rec['status'],len(seen),'modules',rec['overlap_pairs_verified'],'exact overlap pairs')
