# One-shot concrete cost-consumer source union; frozen bounded compiler reused.
from pathlib import Path
import ast,datetime,hashlib,json,os,re,resource,selectors,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5];FLOOR=3*(1<<30)
S=D.parent/'fast_source_pool/build_fast_pool_v2.py'
for n in ast.parse(S.read_text()).body:
 if isinstance(n,ast.FunctionDef) and n.name in {'sha','cap','run'}:exec(compile(ast.Module(body=[n],type_ignores=[]),str(S),'exec'))
M=D.parent/'hard2_query_size/HARD2-SIZE-MANIFEST-v1.json';assert sha(M)=='dbb5959912e70269374cb980a4e0501674bbf65829fb69e1a03b1ec87edf3e3b'
seed=json.loads(M.read_text());P=R/seed['canonical_build'];PA=R/seed['canonical_audit'];seedpins={e['path']:e['sha256'] for e in seed['immutable_files']}
assert shutil.disk_usage(R).free>=FLOOR
B=R/'results'/('algorithm-universal233-ordinary-work-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));B.mkdir();(B/'lean-toolchain').write_bytes((P/'lean-toolchain').read_bytes())
rec=dict(status='FRESH_WORK_COMPONENT_CONTROLS',all_main_milestones='OPEN',independent_acceptance=False,inputs={},controls={},runs=[],source_entries=[],mapping=[])
def save():(B/'certificate-v1.json').write_text(json.dumps(rec,indent=2)+'\n')
for p in [Path(__file__),S,M,D/'TARGET-v1.md']:rec['inputs'][str(p.relative_to(R))]=sha(p)
save()
try:
 T=B/'controls';T.mkdir();(T/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
 for n,src in {'Zero':'namespace WorkImportPlant\ndef value : Nat := 0\nend WorkImportPlant\n','One':'namespace WorkImportPlant\ndef value : Nat := 1\nend WorkImportPlant\n','Twin':'namespace WorkImportPlant\ndef value : Nat := 0\nend WorkImportPlant\n','ProofA':'theorem WorkProofPlant : True := True.intro\n','ProofB':'theorem WorkProofPlant : True := True.intro\n'}.items():
  (T/(n+'.lean')).write_text('import Std\n'+src);run(T,n)
 for n,imports,want in [('ProofTwin',['ProofA','ProofB'],0),('BadLR',['Zero','One'],1),('BadRL',['One','Zero'],1),('IdenticalNP',['Zero','Twin'],1)]:
  (T/(n+'.lean')).write_text(''.join('import '+i+'\n' for i in imports));out=run(T,n,want)
  if want:assert "environment already contains 'WorkImportPlant.value'" in out
  rec['controls'][n]='EXPECTED_IMPORT_RESULT'
 (T/'False.lean').write_text('import Std\nexample : (1:Nat)+1=3 := by decide\n');out=run(T,'False',1);assert 'proved that the proposition' in out and 'sorry' not in out;rec['controls']['false_kernel']='CAUGHT'
 assert sha(T/'Zero.lean')==sha(T/'Twin.lean') and sha(T/'Zero.lean')!=sha(T/'One.lean');rec['controls']['exact_adapted_bytes']='PASS'
 try:assert sha(T/'Zero.lean')=='corrupted'
 except AssertionError:rec['controls']['source_pin']='CAUGHT'
 else:raise AssertionError('CORRUPTED_PIN_ACCEPTED')
 chosen={};bybytes={};source={};resolved={};active=set();new=set()
 saved=json.loads((PA/'certificate.json').read_text());assert sha(PA/'certificate.json')==seedpins[str((PA/'certificate.json').relative_to(R))]
 for e in saved['sources']:
  n=e['module'];p=P/(n+'.lean');o=P/(n+'.olean');assert sha(p)==e['source_sha256']==seedpins[str(p.relative_to(R))] and sha(o)==e['olean_sha256']==seedpins[str(o.relative_to(R))]
  assert p.stat().st_mode&0o222==0 and o.stat().st_mode&0o222==0
  os.link(p,B/p.name);os.link(o,B/o.name)
  chosen[n]=dict(module=n,sha256=sha(p),olean_sha256=sha(o),origins=[dict(package='seed',source=str(p.relative_to(R)),source_sha256=sha(p),original_mode=oct(p.stat().st_mode&0o777),import_adaptations={})],build_mode='EXACT_FROZEN_SOURCE_BINARY_REUSE');bybytes[sha(p)]=n
 configs=[('functional','fast_ordinary_recursion/FINAL-MANIFEST-v1.json','0f806c00eacdc8d3d12ffb9c38406edd0363eb6b5a235897506880fe05efcb8c','results/algorithm-universal233-fast-ordinary-recursion-replay-20261015T205325296780Z',['FastExact']),('forest_polynomial','forest_local_overhead_polynomial/FINAL-MANIFEST-v1.json','161d04f6c3756ee2b9c6b7eb9c08c16006d529edb70ca30a1153914b48af1c9e','results/algorithm-universal233-forest-local-overhead-root-20261015T205439Z',['Monomial'])]
 for pkg,m,h,root,entries in configs:
  p=D.parent/m;assert sha(p)==h;rec['inputs'][str(p.relative_to(R))]=h;pins={e['path']:e['sha256'] for e in json.loads(p.read_text())['immutable_files']};root=R/root
  for p in root.glob('*.lean'):
   if str(p.relative_to(R)) in pins:source[(pkg,p.stem)]=(p,pins[str(p.relative_to(R))])
  for n in entries:assert (pkg,n) in source
 def resolve(key):
  if key in resolved:return resolved[key]
  assert key in source and key not in active,('SOURCE_CLOSURE',key);active.add(key);p,h=source[key];assert sha(p)==h;changes={};lines=[]
  for line in p.read_text().splitlines(keepends=True):
   if line.startswith('import '):
    m=re.fullmatch(r'import ([A-Za-z0-9_\'.]+)\s*',line);assert m,(key,line);dep=m[1]
    if dep.split('.')[0] not in {'Std','Lean','Init'}:
     alias=resolve((key[0],dep))
     if alias!=dep:line='import '+alias+'\n';changes[dep]=alias
   lines.append(line)
  data=''.join(lines).encode();ah=hashlib.sha256(data).hexdigest();origin=dict(package=key[0],source=str(p.relative_to(R)),source_sha256=h,original_mode=oct(p.stat().st_mode&0o777),import_adaptations=changes)
  if ah in bybytes:n=bybytes[ah];chosen[n]['origins'].append(origin)
  else:
   n=key[1]
   if n in chosen:n='Work'+''.join(x.title() for x in key[0].split('_'))+n
   assert n not in chosen and not (B/(n+'.lean')).exists();(B/(n+'.lean')).write_bytes(data);new.add(n);bybytes[ah]=n;chosen[n]=dict(module=n,sha256=ah,origins=[origin],build_mode='NEW_ADAPTED_SOURCE_BUILD')
  active.remove(key);resolved[key]=n;rec['mapping'].append(dict(package=key[0],original_module=key[1],selected_module=n));return n
 roots=['PaidTargets']
 for pkg,m,h,root,entries in configs:
  for n in entries:roots.append(resolve((pkg,n)))
 order=[];seen=set()
 def visit(n):
  if n in seen:return
  p=B/(n+'.lean');assert sha(p)==chosen[n]['sha256']
  for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
   if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
  seen.add(n);order.append(n)
 for n in roots:visit(n)
 rec.update(status='ACTUAL_WORK_COMPONENT_BUILD',source_entries=[chosen[n] for n in order],new_modules=[n for n in order if n in new],consumer_modules=roots);save();print('WORK_COMPONENTS',len(order),'NEW',len(new),flush=True)
 for n in rec['new_modules']:run(B,n);chosen[n]['olean_sha256']=sha(B/(n+'.olean'));save();print('BUILT',n,flush=True)
 (B/'WorkComponentsV1.lean').write_text(''.join('import '+n+'\n' for n in roots));run(B,'WorkComponentsV1');rec.update(status='PASS_AUTHOR_WORK_COMPONENT_BUILD_PENDING_ACTUAL_CONSUMERS_AUDIT',source_entries=[chosen[n] for n in order]);save();print(rec['status'],flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-BUILD-v1.json').write_text(json.dumps(dict(directory=str(B.relative_to(R)),certificate_sha256=sha(B/'certificate-v1.json')),indent=2)+'\n')
