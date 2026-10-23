# One-shot work-consumer extension, reusing the frozen exact source resolver.
from pathlib import Path
import ast,datetime,hashlib,json,os,re,resource,selectors,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5];FLOOR=3*(1<<30)
B=R/json.loads((D/'LATEST-BUILD-v1.json').read_text())['directory'];C=B/'rule5-extension-v1';C.mkdir()
S=D.parent/'fast_source_pool/build_fast_pool_v2.py';X=D.parent/'hard2_dispatch/extend_final_handlers_v1.py'
for n in ast.parse(S.read_text()).body:
 if isinstance(n,ast.FunctionDef) and n.name in {'sha','cap','run'}:exec(compile(ast.Module(body=[n],type_ignores=[]),str(S),'exec'))
base=json.loads((B/'certificate-v1.json').read_text());assert base['status']=='PASS_AUTHOR_WORK_COMPONENT_BUILD_PENDING_ACTUAL_CONSUMERS_AUDIT'
base['source_entries']+=[dict(module='WorkComponentsV1',sha256=sha(B/'WorkComponentsV1.lean'),origins=[])]
rec=dict(status='FRESH_RULE5_WORK_EXTENSION_CONTROLS',all_main_milestones='OPEN',independent_acceptance=False,inputs={},controls={},runs=[],source_entries=[],mapping=[],frozen_source_modes=[])
def save():(C/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
for p in [Path(__file__),S,X,B/'certificate-v1.json']:rec['inputs'][str(p.relative_to(R))]=sha(p)
save()
try:
 T=C/'controls';T.mkdir();(T/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
 for n,src in {'Zero':'namespace WorkExtensionPlant\ndef value : Nat := 0\nend WorkExtensionPlant\n','One':'namespace WorkExtensionPlant\ndef value : Nat := 1\nend WorkExtensionPlant\n','Twin':'namespace WorkExtensionPlant\ndef value : Nat := 0\nend WorkExtensionPlant\n','ProofA':'theorem WorkExtensionProof : True := True.intro\n','ProofB':'theorem WorkExtensionProof : True := True.intro\n'}.items():
  (T/(n+'.lean')).write_text('import Std\n'+src);run(T,n)
 for n,imps,want in [('ProofTwin',['ProofA','ProofB'],0),('BadLR',['Zero','One'],1),('BadRL',['One','Zero'],1),('IdenticalNP',['Zero','Twin'],1)]:
  (T/(n+'.lean')).write_text(''.join('import '+i+'\n' for i in imps));out=run(T,n,want)
  if want:assert "environment already contains 'WorkExtensionPlant.value'" in out
  rec['controls'][n]='EXPECTED_IMPORT_RESULT'
 assert sha(T/'Zero.lean')==sha(T/'Twin.lean') and sha(T/'Zero.lean')!=sha(T/'One.lean');rec['controls']['exact_adapted_bytes']='PASS'
 M=D.parent/'rule5_actual_trace/FINAL-MANIFEST-v1.json';assert sha(M)=='f64fc034cdc6ceb49734c7ad2b558e04dcef39c4f424080b328e40c520f080ba';rec['inputs'][str(M.relative_to(R))]=sha(M)
 pins={e['path']:e['sha256'] for e in json.loads(M.read_text())['immutable_files']}
 P=R/'results/algorithm-universal233-rule5-actual-trace-replay-20261015T211517044108Z'
 chosen={e['module']:dict(e) for e in base['source_entries']};bybytes={e['sha256']:e['module'] for e in base['source_entries']};source={};resolved={};active=set();new=set()
 for e in base['source_entries']:assert sha(B/(e['module']+'.lean'))==e['sha256']
 for p in P.glob('*.lean'):
  rel=str(p.relative_to(R))
  if rel in pins:
   source[('rule5_trace',p.stem)]=(p,pins[rel]);rec['frozen_source_modes'].append(dict(path=rel,sha256=pins[rel],mode=oct(p.stat().st_mode&0o777)))
 functions=[n for n in ast.walk(ast.parse(X.read_text())) if isinstance(n,ast.FunctionDef) and n.name in {'resolve','visit'}];assert len(functions)==2
 exec(compile(ast.Module(body=functions,type_ignores=[]),str(X),'exec'),globals())
 root=resolve(('rule5_trace','WorkBinding'));order=[];seen=set()
 visit('WorkComponentsV1');visit(root)
 master='WorkComponentsV2';assert not (B/(master+'.lean')).exists();(B/(master+'.lean')).write_text('import WorkComponentsV1\nimport '+root+'\n')
 rec.update(status='ACTUAL_RULE5_WORK_EXTENSION_BUILD',source_entries=[chosen[n] for n in order],new_modules=[n for n in order if n in new],consumer_modules=['WorkComponentsV1',root],master_module=master);save();print('WORK_RULE5_EXTENSION',len(order),'NEW',len(new),flush=True)
 for n in rec['new_modules']:run(B,n);save();print('BUILT',n,flush=True)
 run(B,master);rec['status']='PASS_AUTHOR_WORK_RULE5_EXTENSION_PENDING_ACTUAL_CONSUMER_AUDIT';save();print(rec['status'],flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-EXTENSION-v1.json').write_text(json.dumps(dict(directory=str(B.relative_to(R)),certificate=str((C/'certificate.json').relative_to(R)),certificate_sha256=sha(C/'certificate.json')),indent=2)+'\n')
