# Add the completed common-branch producer from the SAME frozen hard2 context.
from pathlib import Path
import hashlib,json,os,re,stat
D=Path(__file__).resolve().parent;R=D.parents[5];B=D/'build'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
M=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/ordinary_hard2_source_work_20261016T095230Z/FINAL-MANIFEST-v1.json';assert sha(M)=='527e2ccd8d61b520dfd46620db4e0cd3f15287ad7ebe1a35b1fbd0ec9522a40b';m=json.loads(M.read_text());P=R/m['canonical_build'];pins={e['path']:e for e in m['immutable_files']};rec=json.loads((D/'DEPENDENCY-PROVENANCE-v1.json').read_text());seen={e['module']:e for e in rec['modules']};visited=set()
def add(n):
 if n in visited:return
 visited.add(n);p=P/(n+'.lean');o=P/(n+'.olean')
 for f in [p,o]:assert sha(f)==pins[str(f.relative_to(R))]['sha256'] and not f.stat().st_mode&0o222
 for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
  if dep.split('.')[0] not in {'Init','Std','Lean'}:add(dep)
 if n in seen:
  assert sha(p)==seen[n]['source']['sha256'] and sha(o)==seen[n]['object']['sha256'];return
 e={'module':n,'package':'hard2_front_common_branch'}
 for k,f in [('source',p),('object',o)]:
  s=f.stat();e[k]={'path':str(f.relative_to(R)),'sha256':sha(f),'mode':oct(stat.S_IMODE(s.st_mode)),'inode':s.st_ino,'bytes':s.st_size};os.link(f,B/f.name)
 rec['modules'].append(e);seen[n]=e
add('CommonBranchWork');rec['common_extension']='Exact frozen common branch, identical overlapping source/object pairs';(D/'DEPENDENCY-PROVENANCE-v2.json').write_text(json.dumps(rec,indent=2)+'\n');print('EXACT_COMMON_CONTEXT_EXTENSION',len(seen))
