# One-shot concrete allGood guard dependency union; frozen resolver/compiler reused.
from pathlib import Path
import ast,datetime,hashlib,json,os,re,resource,selectors,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5];FLOOR=3*(1<<30)
B=R/json.loads((D/'LATEST-BUILD-v1.json').read_text())['directory'];C=B/'checker-extension-v1';C.mkdir()
S=D.parent/'fast_source_pool/build_fast_pool_v2.py';X=D.parent/'hard2_dispatch/extend_final_handlers_v1.py'
for n in ast.parse(S.read_text()).body:
 if isinstance(n,ast.FunctionDef) and n.name in {'sha','cap','run'}:exec(compile(ast.Module(body=[n],type_ignores=[]),str(S),'exec'))
seed=json.loads((B/'SEED-RECEIPT.json').read_text());assert seed['status']=='PASS_EXACT_READONLY_SOURCE_SEED'
rec=dict(status='FRESH_DP_CHECKER_UNION_CONTROLS',all_main_milestones='OPEN',independent_acceptance=False,inputs={},controls={},runs=[],source_entries=[],mapping=[])
def save():(C/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
for p in [Path(__file__),S,X,B/'SEED-RECEIPT.json']:rec['inputs'][str(p.relative_to(R))]=sha(p)
save()
try:
 T=C/'controls';T.mkdir();(T/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
 for n,src in {'Zero':'namespace DPUnionPlant\ndef value : Nat := 0\nend DPUnionPlant\n','One':'namespace DPUnionPlant\ndef value : Nat := 1\nend DPUnionPlant\n','Twin':'namespace DPUnionPlant\ndef value : Nat := 0\nend DPUnionPlant\n','ProofA':'theorem DPUnionProof : True := True.intro\n','ProofB':'theorem DPUnionProof : True := True.intro\n'}.items():
  (T/(n+'.lean')).write_text('import Std\n'+src);run(T,n)
 for n,imps,want in [('ProofTwin',['ProofA','ProofB'],0),('BadLR',['Zero','One'],1),('BadRL',['One','Zero'],1),('IdenticalNP',['Zero','Twin'],1)]:
  (T/(n+'.lean')).write_text(''.join('import '+i+'\n' for i in imps));out=run(T,n,want)
  if want:assert "environment already contains 'DPUnionPlant.value'" in out
  rec['controls'][n]='EXPECTED_IMPORT_RESULT'
 assert sha(T/'Zero.lean')==sha(T/'Twin.lean') and sha(T/'Zero.lean')!=sha(T/'One.lean');rec['controls']['exact_adapted_bytes']='PASS'
 M=D.parent/'forest_check_correspondence/FINAL-MANIFEST-v1.json';assert sha(M)=='d4075adc059fde5b479710126cb73bd8bc55c2475dc668de98c2e4890c23195f';rec['inputs'][str(M.relative_to(R))]=sha(M)
 pins={e['path']:e['sha256'] for e in json.loads(M.read_text())['immutable_files']};P=R/'results/algorithm-universal233-forest-check-root-20261015T211023Z'
 chosen={e['module']:dict(module=e['module'],sha256=e['source_sha256'],olean_sha256=e['olean_sha256'],origins=[]) for e in seed['sources']};bybytes={e['sha256']:e['module'] for e in chosen.values()};source={};resolved={};active=set();new=set()
 for p in P.glob('*.lean'):
  rel=str(p.relative_to(R))
  if rel in pins:source[('checker',p.stem)]=(p,pins[rel])
 functions=[n for n in ast.walk(ast.parse(X.read_text())) if isinstance(n,ast.FunctionDef) and n.name in {'resolve','visit'}];assert len(functions)==2
 exec(compile(ast.Module(body=functions,type_ignores=[]),str(X),'exec'),globals())
 root=resolve(('checker','CheckBounds'));order=[];seen=set();visit('WorkControls');visit(root)
 master='DPCheckerComponentsV1';(B/(master+'.lean')).write_text('import WorkControls\nimport '+root+'\n')
 rec.update(status='ACTUAL_DP_CHECKER_UNION_BUILD',source_entries=[chosen[n] for n in order],new_modules=[n for n in order if n in new],consumer_modules=['WorkControls',root],master_module=master);save();print('DP_CHECKER_UNION',len(order),'NEW',len(new),flush=True)
 for n in rec['new_modules']:run(B,n);save();print('BUILT',n,flush=True)
 run(B,master);rec['status']='PASS_AUTHOR_DP_CHECKER_UNION_PENDING_CONSUMER_AUDIT';save();print(rec['status'],flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-EXTENSION-v1.json').write_text(json.dumps(dict(directory=str(B.relative_to(R)),certificate=str((C/'certificate.json').relative_to(R)),certificate_sha256=sha(C/'certificate.json')),indent=2)+'\n')
