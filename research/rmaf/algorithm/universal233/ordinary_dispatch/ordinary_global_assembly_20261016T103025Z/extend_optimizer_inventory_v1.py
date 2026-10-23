# Exact original-context source/object inventory. Object differences are retained
# as unaccepted compatibility obligations, never silently flattened.
from pathlib import Path
import hashlib,json,os,re,stat
D=Path(__file__).resolve().parent;R=D.parents[5];B=D/'build'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
t=json.loads((R/'research/rmaf/monitoring/next-20261016T103025Z/GLOBAL-COST-ASSEMBLY-TARGET-v1.json').read_text());pins={}
for n in ['optimizer_fees','actual_recovery_source','optimizer','early','checker','functional']:
 e=t['allowed_packages'][n];p=R/e['manifest'];assert sha(p)==e['sha256'];m=json.loads(p.read_text())
 for x in m.get('immutable_files',[])+m.get('original_files',[]):
  if x['path'] not in pins:pins[x['path']]=x
roots=[R/p for p in ['results/algorithm-universal233-recovery-source-20261016T092054Z-20261016T092457019053Z','results/algorithm-universal233-optimizer-local-20261016T085144Z-20261016T085502958188Z','results/algorithm-universal233-early-resume-20261016T083330Z-20261016T083634190186Z','results/algorithm-universal233-budget-optimization-replay-20261015T213529360638Z','results/algorithm-universal233-forest-check-root-20261015T211023Z']]
rec=json.loads((D/'DEPENDENCY-PROVENANCE-v2.json').read_text());seen={e['module']:e for e in rec['modules']};visited=set();alt=[];extra=[]
def add(n):
 if n in visited:return
 visited.add(n);root=next((p for p in roots if (p/(n+'.olean')).exists()),None);assert root is not None,('NO_ORIGINAL_CONTEXT_OBJECT',n)
 p=root/(n+'.lean');o=root/(n+'.olean');assert p.exists(),('NO_ORIGINAL_SOURCE',n,root)
 for f in [p,o]:
  e=pins.get(str(f.relative_to(R)));assert e and sha(f)==e['sha256'],('UNPINNED_OR_DRIFT',n,str(f))
  assert not f.stat().st_mode&0o222,('ORIGINAL_SOURCE_NOT_SEALED',str(f))
 for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
  if dep.split('.')[0] not in {'Init','Std','Lean'}:add(dep)
 e={'module':n,'package':'optimizer_recovery_original_context'}
 for k,f in [('source',p),('object',o)]:
  z=f.stat();e[k]={'path':str(f.relative_to(R)),'sha256':sha(f),'mode':oct(stat.S_IMODE(z.st_mode)),'inode':z.st_ino,'bytes':z.st_size}
 if n in seen:
  old=seen[n];assert e['source']['sha256']==old['source']['sha256'],('SOURCE_MISMATCH',n)
  if e['object']['sha256']!=old['object']['sha256']:alt.append({'module':n,'chosen':old,'alternative':e})
  return
 for f in [p,o]:os.link(f,B/f.name)
 seen[n]=e;rec['modules'].append(e);extra.append(n)
for n in ['RWInterface','OWBudgets']:add(n)
rec['optimizer_context']={'roots':[str(p.relative_to(R)) for p in roots],'visited_original_modules':len(visited),'new_modules':extra,'object_differences':alt,'decision':'UNACCEPTED_PENDING_EXACT_TYPE_NONPROOF_BODY_AND_FULL_METADATA_COMPARISON' if alt else 'IDENTICAL_OVERLAPS'}
(D/'DEPENDENCY-PROVENANCE-v3.json').write_text(json.dumps(rec,indent=2)+'\n');print('CONTEXT_INVENTORY',len(seen),'modules','new',extra,'object_differences',[e['module'] for e in alt])
