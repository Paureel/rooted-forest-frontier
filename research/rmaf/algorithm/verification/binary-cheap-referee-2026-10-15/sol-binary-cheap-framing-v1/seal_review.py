"""One-shot SHA256 seal for this framing review; no scientific replay."""
from pathlib import Path
import hashlib
import json

own=Path(__file__).resolve().parent
entries=[]
for path in sorted(own.iterdir()):
    if path.is_file() and path.name not in ['MANIFEST.json','MANIFEST.sha256']:
        raw=path.read_bytes()
        entries.append({'path':path.name,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
data={
    'schema':'binary-cheap-fresh-context-framing-review/v1',
    'scope':'Reader-inference review of sealed graph/local-certificate/raw-list interfaces; no kernel replay or new mathematical replication',
    'no_further_writes':True,
    'author_manifest_sha256':'3936cb4b0a5d390972ad7b1fdace4166faa9a372cc9232329294a0f2b346d839',
    'source_review_manifest_sha256':'c95942cce328646d13ab78f23313ff8cbb94ae576d8e6ab8ff1c243591768ee0',
    'findings':[{'id':'F1','severity':'MEDIUM','kind':'documentation prominence','subject':'accepted geometry versus AF'}, {'id':'F2','severity':'MEDIUM','kind':'documentation prominence','subject':'cross-group clearance versus within-B overlap'}, {'id':'F3','severity':'MEDIUM','kind':'documentation prominence','subject':'merged names versus stored producer occurrences'}],
    'theorem_refutation_established':False,
    'replication_increment':0,
    'all_three_main_milestones':'OPEN',
    'novelty':'OPEN; not assessed by a literature campaign',
    'different_eyes_final_diff_review':'OUTSTANDING for root; two same-editor passes retained',
    'contacts':'No author, other reviewer or child contacts; no children spawned',
    'writes':'Owned local review directory only; frozen reports and sources unchanged',
    'entry_count':len(entries),
    'entries':entries,
}
manifest=own/'MANIFEST.json'
manifest.write_text(json.dumps(data,indent=2)+'\n')
digest=hashlib.sha256(manifest.read_bytes()).hexdigest()
(own/'MANIFEST.sha256').write_text(digest+'  MANIFEST.json\n')
for entry in entries:
    assert hashlib.sha256((own/entry['path']).read_bytes()).hexdigest()==entry['sha256']
print(json.dumps({'entry_count':len(entries),'manifest_sha256':digest,'entry_hashes_verified':True},indent=2))
