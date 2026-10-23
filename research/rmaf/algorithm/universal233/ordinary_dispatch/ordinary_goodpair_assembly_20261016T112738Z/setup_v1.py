# Selected exact contexts only. Different overlapping objects remain unaccepted
# until original-context declaration and complete metadata comparison.
from pathlib import Path
import hashlib,json,os,re,shutil,stat
D=Path(__file__).resolve().parent;R=D.parents[5];B=D/'build';assert not B.exists();assert shutil.disk_usage(R).free>=3*(1<<30);B.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
t=json.loads((R/'research/rmaf/monitoring/cost-width-next-20261016T112738Z/GOODPAIR-RULE5-ASSEMBLY-TARGET-v2.json').read_text());ms={};filepins={}
for k,e in t['allowed_packages'].items():
 p=R/e['manifest'];assert sha(p)==e['sha256'];m=json.loads(p.read_text());ms[k]=m
 for x in m.get('immutable_files',[])+m.get('immutable_owned_files',[])+m.get('original_files',[]):filepins.setdefault(x['path'],x)
# Old pool hardlinks are licensed through its sealed exact provenance.
prev=ms['completed_extended_assembly'];P=R/prev['canonical_build'];pd=json.loads((R/prev['dependency_provenance']).read_text())
for e in pd['modules']:
 for kind in ['source','object']:
  x=e[kind];p=P/(e['module']+('.lean' if kind=='source' else '.olean'));q=R/x['path'];assert p.stat().st_ino==q.stat().st_ino or not p.stat().st_mode&0o222
  filepins.setdefault(str(p.relative_to(R)),{'path':str(p.relative_to(R)),'sha256':x['sha256'],'inode':p.stat().st_ino,'mode':oct(stat.S_IMODE(p.stat().st_mode))})
r5=json.loads((R/ms['new_closed_rule5_local_source']['public_interface']['path']).read_text())
contexts={'previous':[P],'goodpair':[R/ms['new_completed_goodpair_prepare']['canonical_build']],'numeric':[R/ms['numeric_semantic']['canonical_build'],R/ms['numeric_semantic']['source_pool']],'rule5_closed':[R/p for p in r5['import_paths']]}
r5c=R/r5['certificate']['path'];assert sha(r5c)==r5['certificate']['sha256'];certdeps={'rule5_closed':json.loads(r5c.read_text())['dependencies']}
seen={};visited=set();alternatives=[];rec={'version':1,'status':'CHECKING','modules':[],'contexts':{k:[str(p.relative_to(R)) for p in v] for k,v in contexts.items()},'overlap_exact_pairs':0,'object_differences':alternatives}
def save():(D/'DEPENDENCY-PROVENANCE-v1.json').write_text(json.dumps(rec,indent=2)+'\n')
save()
def add(n,package):
 if (n,package) in visited:return
 visited.add((n,package));roots=contexts[package];root=next((p for p in roots if (p/(n+'.olean')).exists()),None);assert root,('NO_CONTEXT_OBJECT',n,package)
 p=root/(n+'.lean');o=root/(n+'.olean')
 if not p.exists():
  x=certdeps[package][n];assert sha(o)==x['loaded_sha256'];assert o.resolve()==(R/x['loaded_olean']).resolve();p=R/x['source'];assert sha(p)==x['source_sha256']
 assert p.exists(),('NO_CONTEXT_SOURCE',n,package)
 e={'module':n,'package':package}
 for kind,f in [('source',p),('object',o)]:
  x=filepins.get(str(f.relative_to(R)));assert x,('UNPINNED_FILE',str(f));assert sha(f)==x['sha256'],('PIN_HASH',str(f));z=f.stat();mode=oct(stat.S_IMODE(z.st_mode));want=x.get('mode');assert want is None or mode==(oct(stat.S_IMODE(want)) if isinstance(want,int) else want),('PIN_MODE',str(f));assert z.st_ino==x.get('inode',z.st_ino),('PIN_INODE',str(f));e[kind]={'path':str(f.relative_to(R)),'sha256':sha(f),'mode':mode,'inode':z.st_ino,'bytes':z.st_size}
 for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
  if dep.split('.')[0] not in {'Init','Std','Lean'}:add(dep,package)
 if n in seen:
  assert e['source']['sha256']==seen[n]['source']['sha256'],('SOURCE_DIFFERENCE',n,package)
  if e['object']['sha256']!=seen[n]['object']['sha256']:alternatives.append({'module':n,'package':package,'chosen':seen[n],'alternative':e})
  else:rec['overlap_exact_pairs']+=1
  return
 for f in [p,o]:
  q=B/f.name
  if f.stat().st_mode&0o222:q.write_bytes(f.read_bytes());q.chmod(0o444)
  else:os.link(f,q)
 seen[n]=e;rec['modules'].append(e)
for package,roots in [('previous',['ExtendedSourceInterface']),('goodpair',['GoodPairSelectedBound']),('numeric',['NumericReach']),('rule5_closed',['RefusalAndDomains'])]:
 for n in roots:add(n,package)
shutil.copyfile(P/'lean-toolchain',B/'lean-toolchain');rec['status']='UNACCEPTED_OBJECT_DIFFERENCES' if alternatives else 'PASS_EXACT_IDENTICAL_CONTEXT';save();(D/'BUILD-v1.json').write_text(json.dumps({'directory':str(B.relative_to(R))},indent=2)+'\n');print(rec['status'],len(seen),'modules',rec['overlap_exact_pairs'],'exact overlaps',len(alternatives),'different objects');print('NEW',[e['module'] for e in rec['modules'] if e['package']!='previous'])
