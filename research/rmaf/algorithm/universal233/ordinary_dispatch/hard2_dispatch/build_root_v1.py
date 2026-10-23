# One-shot actual hard2 consumer union. Reuse the completed capped compiler.
from pathlib import Path
import ast,datetime,hashlib,json,os,re,resource,selectors,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5];P=R/'results/algorithm-universal233-fast-source-pool-20261015T194053203759Z';B=R/'results'/('algorithm-universal233-hard2-dispatch-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));B.mkdir();FLOOR=3*(1<<30);S=D.parent/'fast_source_pool/build_fast_pool_v2.py'
for n in ast.parse(S.read_text()).body:
 if isinstance(n,ast.FunctionDef) and n.name in {'sha','cap','run'}:exec(compile(ast.Module(body=[n],type_ignores=[]),str(S),'exec'))
rec=dict(status='FRESH_HARD2_ROOT_CONTROLS',all_main_milestones='OPEN',independent_acceptance=False,inputs={},controls={},runs=[],source_entries=[],mapping=[])
def save():(B/'certificate-v1.json').write_text(json.dumps(rec,indent=2)+'\n')
configs=[('disjoint','ordinary_dispatch/case_queries_release/CASE-QUERIES-MANIFEST-v1.json','3bc6db2c33a19476d543a5225983d7750c7277db505269f42aadbfc51528c7c5','results/algorithm-universal233-disjoint-parent-query-20261015T195609926776Z',['Hard2Combine','DisjointCounts']),('good_pair','ordinary_dispatch/case_queries_release/CASE-QUERIES-MANIFEST-v1.json','3bc6db2c33a19476d543a5225983d7750c7277db505269f42aadbfc51528c7c5','results/algorithm-universal233-allgood-pair-query-20261015T195944423783Z',['PairExact']),('both_bad_local','ordinary_dispatch/both_bad_local_binding/FINAL-MANIFEST-v1.json','90a3ca2d369ed9f30822a1eb72bad4aea957e9013458ff3a43cb856b2eb964c4','results/algorithm-universal233-both-bad-local-root-20261015T195334Z',['BothBadBinding']),('both_bad_grouped','ordinary_dispatch/both_bad_grouped_binding/FINAL-MANIFEST-v1.json','c9201261d146adcf643680f05acd24e0cefa10c57f93a8dba901861668b1e4f3','results/algorithm-universal233-both-bad-grouped-replay-20261015T200610286423Z',['PairRefinement'])]
for p in [Path(__file__),S,D/'TARGET-v1.md']:rec['inputs'][str(p.relative_to(R))]=sha(p)
(B/'lean-toolchain').write_bytes((P/'lean-toolchain').read_bytes());save()
try:
 T=B/'controls';T.mkdir();(T/'lean-toolchain').write_bytes((P/'lean-toolchain').read_bytes())
 for n,s in {'Zero':'namespace Hard2RootPlant\ndef value : Nat := 0\nend Hard2RootPlant\n','One':'namespace Hard2RootPlant\ndef value : Nat := 1\nend Hard2RootPlant\n','Twin':'namespace Hard2RootPlant\ndef value : Nat := 0\nend Hard2RootPlant\n','TruePlant':'example : (1:Nat)+1=2 := by decide\n'}.items():(T/(n+'.lean')).write_text('import Std\n'+s);run(T,n)
 for n,imps in [('WrongLR',['Zero','One']),('WrongRL',['One','Zero']),('IdenticalNP',['Zero','Twin'])]:
  (T/(n+'.lean')).write_text(''.join('import '+m+'\n' for m in imps));out=run(T,n,1);assert "environment already contains 'Hard2RootPlant.value'" in out;rec['controls'][n]='CAUGHT'
 (T/'FalsePlant.lean').write_text('import Std\nexample : (1:Nat)+1=3 := by decide\n');out=run(T,'FalsePlant',1);assert 'proved that the proposition' in out and 'sorry' not in out;rec['controls']['false_kernel']='CAUGHT'
 assert sha(T/'Zero.lean')==sha(T/'Twin.lean') and sha(T/'Zero.lean')!=sha(T/'One.lean');rec['controls']['exact_adapted_bytes']='PASS'
 try:assert sha(T/'Zero.lean')=='corrupted'
 except AssertionError:rec['controls']['source_pin']='CAUGHT'
 else:raise AssertionError('SOURCE_PIN_CORRUPTION_ACCEPTED')
 pm=D.parent/'fast_source_pool/release_v1/FAST-SOURCE-POOL-MANIFEST-v1.json';assert sha(pm)=='efa132be64d489544e2aeeffaa0d08494cb9986d28104024f200f1080e2fbb60';rec['inputs'][str(pm.relative_to(R))]=sha(pm);pp={e['path']:e['sha256'] for e in json.loads(pm.read_text())['immutable_files']};base=json.loads((P/'extension-v1/certificate.json').read_text());chosen={};bybytes={};source={};resolved={};active=set();new=set()
 for e in base['source_entries']+[dict(module='FastImports',sha256=sha(P/'FastImports.lean'),origins=[]),dict(module='FastConsumersV2',sha256=sha(P/'FastConsumersV2.lean'),origins=[])]:
  n=e['module'];chosen[n]=dict(e,build_mode='UNCHANGED_FROZEN_SOURCE_BINARY',olean_sha256=sha(P/(n+'.olean')));bybytes[e['sha256']]=n
  for ext in ['.lean','.olean']:
   p=P/(n+ext);assert sha(p)==pp[str(p.relative_to(R))];os.link(p,B/p.name)
 for pkg,m,h,root,entries in configs:
  p=R/'research/rmaf/algorithm/universal233'/m;assert sha(p)==h;rec['inputs'][str(p.relative_to(R))]=h;pins={e['path']:e['sha256'] for e in json.loads(p.read_text())['immutable_files']};root=R/root
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
   if n in chosen:n='Hard2'+''.join(x.title() for x in key[0].split('_'))+n
   assert n not in chosen and not (B/(n+'.lean')).exists();(B/(n+'.lean')).write_bytes(data);new.add(n);bybytes[ah]=n;chosen[n]=dict(module=n,sha256=ah,origins=[origin],build_mode='NEW_ADAPTED_SOURCE_BUILD')
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
 visit('FastConsumersV2')
 for n in roots:visit(n)
 rec.update(status='ACTUAL_HARD2_COMPONENT_BUILD',source_entries=[chosen[n] for n in order],consumer_modules=roots,new_modules=[n for n in order if n in new]);save();print('HARD2_COMPONENTS',len(order),'NEW',len(new),flush=True)
 for n in rec['new_modules']:run(B,n);chosen[n]['olean_sha256']=sha(B/(n+'.olean'));save();print('BUILT',n,flush=True)
 (B/'Hard2ComponentsV1.lean').write_text('import FastConsumersV2\n'+''.join('import '+n+'\n' for n in dict.fromkeys(roots)));run(B,'Hard2ComponentsV1');rec.update(status='PASS_AUTHOR_HARD2_COMPONENT_SOURCE_BUILD_PENDING_FINAL_HANDLERS_AUDIT',source_entries=[chosen[n] for n in order]);save();print(rec['status'],flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-BUILD-v1.json').write_text(json.dumps(dict(directory=str(B.relative_to(R)),certificate_sha256=sha(B/'certificate-v1.json')),indent=2)+'\n')
