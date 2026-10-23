#!/usr/bin/env python3
"""One-shot released-byte verification; no checker/code reuse."""
import hashlib,json,pathlib,re,shutil
HERE=pathlib.Path(__file__).resolve().parent; ROOT=HERE.parents[5]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
release=[('research/rmaf/algorithm/universal233/state_reductions/STATE-MANIFEST-v1.json','9a85af84a6cd917af0780c4c12ab356897a7e416b402fa3f875250487f7c29f6',77),('research/rmaf/algorithm/universal233/state_cherry_completion/CHERRY-MANIFEST-v1.json','b9d584872792f5d6b8c00509c56160c47ac62732ef9a44f7c21c3b5717d53147',103)]
receipts=[]; allfiles={}; modulepaths={}
for mp,digest,count in release:
 assert sha(ROOT/mp)==digest,mp
 m=json.loads((ROOT/mp).read_text()); rows=m['immutable_files']; assert len(rows)==count
 assert len({r['path'] for r in rows})==count
 for r in rows:
  assert sha(ROOT/r['path'])==r['sha256'],r['path']
  if r['path'] in allfiles: assert allfiles[r['path']]==r['sha256']
  allfiles[r['path']]=r['sha256']
 shutil.copyfile(ROOT/mp,HERE/pathlib.Path(mp).name)
 receipts.append({'manifest':mp,'sha256':digest,'fileCount':count,'allMatched':True})
 # Only canonical result source copies, never author auditor/control implementation.
 canonical=m['canonical_receipt']; cert=json.loads((ROOT/canonical).read_text()); shutil.copyfile(ROOT/canonical,HERE/(pathlib.Path(mp).stem+'-certificate.json'))
 for r in rows:
  p=pathlib.Path(r['path'])
  if p.parent==pathlib.Path(canonical).parent and p.suffix=='.lean':
   if p.stem in ['ModuleInventory','ModulePlantAudit','PlantModel','FalseControl','TrueControl','FalseControls','GraphFalseControls']: continue
   if p.stem in modulepaths: assert sha(ROOT/modulepaths[p.stem])==r['sha256']
   modulepaths[p.stem]=r['path']
print(json.dumps({'manifests':receipts,'candidateModules':modulepaths},indent=2))
# Resolve formal source closure from the actual import headers.
imports={n:re.findall(r'^import\s+(\w+)\s*$',(ROOT/p).read_text(),re.M) for n,p in modulepaths.items()}
required=['CompletionConsumers','Consumers']; order=[]; visiting=set()
def visit(n):
 if n in order: return
 assert n not in visiting,'import cycle'
 assert n in modulepaths,n
 visiting.add(n)
 for d in imports[n]:
  if d!='Std': visit(d)
 visiting.remove(n); order.append(n)
for n in required: visit(n)
build=HERE/'isolated'; build.mkdir(exist_ok=False)
for n in order: shutil.copyfile(ROOT/modulepaths[n],build/(n+'.lean'))
assert not list(build.glob('*.olean'))
result={'manifests':receipts,'allManifestFileCount':len(allfiles),'formalModules':[{ 'module':n,'path':modulepaths[n],'sha256':sha(ROOT/modulepaths[n]),'imports':imports[n]} for n in order],'noScientificOleansCopied':True}
(HERE/'release-integrity-v1.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'RELEASE-BYTES-MATCH','formalModuleCount':len(order),'order':order}))
