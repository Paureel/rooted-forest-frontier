from pathlib import Path
from hashlib import sha256
from datetime import datetime,timezone
import json,re,shutil
H=Path(__file__).resolve().parent;ROOT=H.parents[5];BASE=H.parent
release=json.loads((BASE/'ROOT-RELEASE-v1.json').read_text())
mp=ROOT/release['candidate_manifest'];assert sha256(mp.read_bytes()).hexdigest()==release['candidate_sha256']
manifest=json.loads(mp.read_text());entries=manifest['immutable_files'];assert len(entries)==232
assert len(set(e['path'] for e in entries))==232
for e in entries:assert sha256((ROOT/e['path']).read_bytes()).hexdigest()==e['sha256'],e['path']
rp=BASE/'sol-frozen-ready-v1/READY-MANIFEST-v1.json';assert sha256(rp.read_bytes()).hexdigest()==release['readiness_sha256'];ready=json.loads(rp.read_text());assert len(ready['files'])==157
for e in ready['files']:assert sha256((rp.parent/e['path']).read_bytes()).hexdigest()==e['sha256'],e['path']
assert json.loads((H/'producer-controls-v1/fixed-v1.json').read_text())['status']=='PRODUCER-CONTROLS-PASS'
canonical=ROOT/'results/algorithm-universal233-all-good-20261015T113011Z'
source_entries={Path(e['path']).stem:e for e in entries if str(Path(e['path']).parent)==str(canonical.relative_to(ROOT)) and e['path'].endswith('.lean')}
seen=set();order=[];imports={}
def visit(n):
 if n in seen:return
 seen.add(n);p=ROOT/source_entries[n]['path'];deps=[]
 for line in p.read_text().splitlines():
  if line.startswith('import '):deps.extend(line[7:].split())
 imports[n]=deps
 for d in deps:
  if d in source_entries:visit(d)
  else:assert d=='Std' or d=='Lean' or d.startswith(('Init.','Std.','Lean.')),(n,d)
 order.append(n)
visit('ExactMinimum')
assert len(order)==63
out=H/'isolated';assert not out.exists();out.mkdir()
mapping=[]
for n in order:
 e=source_entries[n];src=ROOT/e['path'];dest=out/(n+'.lean');shutil.copyfile(src,dest)
 assert sha256(dest.read_bytes()).hexdigest()==e['sha256']
 matches=[f['path'] for f in entries if Path(f['path']).name==n+'.lean' and f['sha256']==e['sha256']]
 mapping.append({'module':n,'isolated':str(dest.relative_to(H)),'canonical':e['path'],'sha256':e['sha256'],'identicalReleasedPaths':matches,'imports':imports[n],'adaptation':'literal unchanged source bytes; no imports renamed; no scientific olean copied'})
data={'status':'EXACT-SOURCE-ADOPTED','UTC':datetime.now(timezone.utc).isoformat(),'releaseSHA256':sha256((BASE/'ROOT-RELEASE-v1.json').read_bytes()).hexdigest(),'candidateManifestSHA256':release['candidate_sha256'],'candidateEntriesMatched':232,'readyEntriesMatched':157,'sourceModuleCount':len(order),'order':order,'mapping':mapping,'scientificOleansCopied':False,'controlQualificationPrecededCandidateContact':True,'scope':'ExactMinimum dependency closure only; other released controls/auditors are not used as certifiers.'}
(H/'SOURCE-ADOPTION-v1.json').write_text(json.dumps(data,indent=2)+'\n');print(json.dumps({k:v for k,v in data.items() if k not in ['order','mapping']}))
