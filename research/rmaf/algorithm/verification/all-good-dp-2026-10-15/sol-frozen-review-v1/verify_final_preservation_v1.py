"""One-shot exact hash preservation check; no scientific result interpretation."""
from pathlib import Path
from hashlib import sha256
from datetime import datetime,timezone
import json
H=Path(__file__).resolve().parent;ROOT=H.parents[5]
def digest(p):return sha256(p.read_bytes()).hexdigest()
specs=[
 ('research/rmaf/algorithm/verification/forest-reductions-2026-10-15/sol-frozen-ready-v1/READY-MANIFEST-v1.json','25673f06bb120f25235aba32781acd07654fa44d98e258f96eba74a8fcbfce78','files',264,False),
 ('research/rmaf/algorithm/verification/forest-reductions-2026-10-15/sol-frozen-review-v1/REVIEW-MANIFEST-v1.json','92618ee90023319c7d94732483738756cac35406541d80ca5dfadbc1f0523120','files',147,False),
 ('research/rmaf/algorithm/universal233/state_reductions/STATE-MANIFEST-v1.json','9a85af84a6cd917af0780c4c12ab356897a7e416b402fa3f875250487f7c29f6','immutable_files',77,True),
 ('research/rmaf/algorithm/universal233/state_cherry_completion/CHERRY-MANIFEST-v1.json','b9d584872792f5d6b8c00509c56160c47ac62732ef9a44f7c21c3b5717d53147','immutable_files',103,True),
 ('research/rmaf/algorithm/verification/all-good-dp-2026-10-15/sol-frozen-ready-v1/READY-MANIFEST-v1.json','35fb742ddcaec1747696c48627071510acfe0d94e28acdb92d325e9d23a06bc1','files',157,False),
 ('research/rmaf/algorithm/universal233/all_good_dp/ALL-GOOD-MANIFEST-v1.json','02ad617e00e9b394f25404b4c89fb47fcf3ca92c1323a49f30313ec31f6e70d6','immutable_files',232,True),
]
checked=[]
for rel,pin,key,count,workspace in specs:
 p=ROOT/rel;assert digest(p)==pin,('manifest drift',rel);x=json.loads(p.read_text());assert len(x[key])==count and len({e['path'] for e in x[key]})==count
 base=ROOT if workspace else p.parent
 for e in x[key]:
  f=base/e['path'];assert digest(f)==e['sha256'],('payload drift',str(f))
  if 'bytes' in e:assert f.stat().st_size==e['bytes']
 checked.append({'manifest':rel,'sha256':pin,'entriesMatched':count})
a=json.loads((H/'SOURCE-ADOPTION-v2.json').read_text())
for e in a['mapping']:assert digest(H/e['isolated'])==e['sha256']
for directory,manifest in [(H/'producer-controls-v1','CONTROL-MANIFEST-v1.json'),(H,'COST-CONTROL-MANIFEST-v1.json'),(H,'EXTRA-CONTROL-MANIFEST-v1.json')]:
 x=json.loads((directory/manifest).read_text())
 for e in x['files']:assert digest(directory/e['path'])==e['sha256'],('control drift',manifest,e['path'])
out={'status':'FINAL-PRESERVATION-PASS','checkedUTC':datetime.now(timezone.utc).isoformat(),'frozenSets':checked,'pinnedEntriesMatched':sum(r['entriesMatched'] for r in checked),'adoptedSourceBytesMatched':66,'originalExpectationsUntouched':True,'newControlPinsMatched':True,'authorSourcesEdited':False}
(H/'FINAL-PRESERVATION-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
