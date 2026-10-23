# One-shot source-union extension; reuses the completed bounded compiler unchanged.
from pathlib import Path
import ast,datetime,hashlib,json,os,re,resource,selectors,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5]
B=R/'results/algorithm-universal233-hard2-dispatch-20261015T202301302606Z'
base=json.loads((B/'certificate-v1.json').read_text());FLOOR=3*(1<<30)
base['source_entries'] += [dict(module=n,sha256=hashlib.sha256((B/(n+'.lean')).read_bytes()).hexdigest(),origins=[]) for n in ['Hard2ComponentsV1','PairAdapters']]
base['consumer_modules']=['Hard2ComponentsV1','PairAdapters']
script=D.parent/'fast_source_pool/build_fast_pool_v2.py';tree=ast.parse(script.read_text())
for node in tree.body:
 if isinstance(node,(ast.FunctionDef,ast.AsyncFunctionDef)) and node.name in {'sha','cap','run'}:exec(compile(ast.Module(body=[node],type_ignores=[]),str(script),'exec'))
C=B/'extension-v1';C.mkdir();rec=dict(status='FRESH_EXTENSION_CONTROLS',all_main_milestones='OPEN',independent_acceptance=False,inputs={str(script.relative_to(R)):sha(script),str((B/'certificate-v1.json').relative_to(R)):sha(B/'certificate-v1.json')},controls={},runs=[],source_entries=[],mapping=[])
def save():(C/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
configs=[('rule5_handler','ordinary_dispatch/rule5_ordinary_dispatch/FINAL-MANIFEST-v1.json','4a80b60e293d859e39847e1a37b79d071d6bbe8487ddee1eb904ec3430a0f813','results/algorithm-universal233-rule5-ordinary-dispatch-replay-20261015T202011404223Z',['SelectedInterfaces']),('hard2_paid','ordinary_dispatch/hard2_paid_ordinary_binding/FINAL-MANIFEST-v1.json','66b3a84c39b2aeeae24fcf9bc2fd9d8b972b58c7f610d65d1310301a0a68489e','results/algorithm-universal233-hard2-paid-ordinary-root-20261015T201005Z',['PaidValidity'])]
rec['inputs'][str(Path(__file__).relative_to(R))]=sha(Path(__file__));save()
try:
 T=C/'controls';T.mkdir();(T/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
 for n,src in {'Zero':'namespace ExtensionPlant\ndef value : Nat := 0\nend ExtensionPlant\n','One':'namespace ExtensionPlant\ndef value : Nat := 1\nend ExtensionPlant\n','Twin':'namespace ExtensionPlant\ndef value : Nat := 0\nend ExtensionPlant\n','ProofA':'theorem ExtensionProofPlant : True := True.intro\n','ProofB':'theorem ExtensionProofPlant : True := True.intro\n'}.items():(T/(n+'.lean')).write_text('import Std\n'+src);run(T,n)
 for n,imps,want in [('ProofTwin',['ProofA','ProofB'],0),('WrongLR',['Zero','One'],1),('WrongRL',['One','Zero'],1),('IdenticalNP',['Zero','Twin'],1)]:
  (T/(n+'.lean')).write_text(''.join('import '+m+'\n' for m in imps));out=run(T,n,want)
  if want:assert "environment already contains 'ExtensionPlant.value'" in out
  rec['controls'][n]='PASS_EXPECTED_IMPORT_RESULT'
 assert sha(T/'Zero.lean')==sha(T/'Twin.lean') and sha(T/'Zero.lean')!=sha(T/'One.lean');rec['controls']['adapted_byte_equality']='PASS'
 try:assert sha(T/'Zero.lean')=='corrupted'
 except AssertionError:rec['controls']['corrupted_source_pin']='CAUGHT'
 else:raise AssertionError('CORRUPTED_PIN_ACCEPTED')
 save()
 chosen={e['module']:dict(e) for e in base['source_entries']};bybytes={e['sha256']:e['module'] for e in base['source_entries']};source={};resolved={};active=set();new=set()
 for e in base['source_entries']:assert sha(B/(e['module']+'.lean'))==e['sha256']
 for pkg,m,h,root,entries in configs:
  p=R/'research/rmaf/algorithm/universal233'/m;assert sha(p)==h;rec['inputs'][str(p.relative_to(R))]=h;mf=json.loads(p.read_text());pins={e['path']:e['sha256'] for e in mf['immutable_files']};root=R/root
  for p in root.glob('*.lean'):
   if str(p.relative_to(R)) in pins:source[(pkg,p.stem)]=(p,pins[str(p.relative_to(R))])
  for n in entries:assert (pkg,n) in source
 def resolve(key):
  if key in resolved:return resolved[key]
  assert key not in active and key in source,('SOURCE_CLOSURE',key);active.add(key);p,h=source[key];assert sha(p)==h;changes={};lines=[]
  for line in p.read_text().splitlines(keepends=True):
   if line.startswith('import '):
    m=re.fullmatch(r'import ([A-Za-z0-9_\'.]+)\s*',line);assert m,(key,line);dep=m[1]
    if dep.split('.')[0] not in {'Std','Lean','Init'}:
     n=resolve((key[0],dep))
     if n!=dep:line='import '+n+'\n';changes[dep]=n
   lines.append(line)
  data=''.join(lines).encode();ah=hashlib.sha256(data).hexdigest();origin=dict(package=key[0],source=str(p.relative_to(R)),source_sha256=h,import_adaptations=changes)
  if ah in bybytes:n=bybytes[ah];chosen[n]['origins']=chosen[n]['origins']+[origin]
  else:
   n=key[1]
   if n in chosen:n='Fast'+''.join(s.title() for s in key[0].split('_'))+n
   assert n not in chosen and not (B/(n+'.lean')).exists(),('MODULE_ALIAS_COLLISION',key,n)
   chosen[n]=dict(module=n,sha256=ah,origins=[origin]);bybytes[ah]=n;(B/(n+'.lean')).write_bytes(data);new.add(n)
  resolved[key]=n;active.remove(key);rec['mapping'].append(dict(package=key[0],original_module=key[1],selected_module=n));return n
 roots=[]
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
 for n in base['consumer_modules']:visit(n)
 assert set(chosen)==seen,('OMITTED_BASE',set(chosen)-seen)
 master='Hard2ConsumersV2';assert not (B/(master+'.lean')).exists();(B/(master+'.lean')).write_text('import Hard2ComponentsV1\nimport PairAdapters\n'+''.join('import '+n+'\n' for n in dict.fromkeys(roots)))
 rec.update(status='AUTHOR_EXTENSION_BUILD',source_entries=[chosen[n] for n in order],new_modules=[n for n in order if n in new],consumer_modules=list(dict.fromkeys(base['consumer_modules']+roots)),imported_modules=len(order),master_module=master);save();print('EXTENSION_STAGED',len(order),'new',len(new),flush=True)
 for i,n in enumerate(rec['new_modules']):run(B,n);print('EXTENSION_BUILT',i+1,len(new),n,flush=True)
 run(B,master);rec.update(status='PASS_AUTHOR_EXTENDED_ONE_ROOT_PENDING_PRODUCER_AUDIT',unchanged_hard2_component_certificate_sha256=sha(B/'certificate-v1.json'));save();print(rec['status'],len(order),flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-EXTENSION-v1.json').write_text(json.dumps(dict(directory=str(B.relative_to(R)),certificate=str((C/'certificate.json').relative_to(R)),certificate_sha256=sha(C/'certificate.json')),indent=2)+'\n')
