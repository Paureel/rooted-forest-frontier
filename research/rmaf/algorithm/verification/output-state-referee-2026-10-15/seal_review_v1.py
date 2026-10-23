"""One-use local output manifest, separate from all frozen scientific seals."""
from pathlib import Path
import hashlib
import json

OUT = Path(__file__).resolve().parent
items = {}
for path in sorted(OUT.iterdir()):
    if path.is_file() and path.name not in ('MANIFEST.json','MANIFEST.sha256'):
        data = path.read_bytes()
        items[path.name] = {'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
manifest = {
    'status':'FRAME_REVIEW_COMPLETED_WITH_PROPOSED_SCOPE_CORRECTIONS',
    'scope':'seven sealed documents; named source/type/receipt spot checks only',
    'separate_from_earlier_121_module_audit':True,
    'fresh_kernel_replay':False,
    'independent_mathematical_replications_added':0,
    'new_theorem_or_solver':False,
    'global_algorithm_runtime_novelty_closure':False,
    'all_three_main_milestones':'OPEN',
    'novelty':'OPEN',
    'frozen_source_documents_edited':False,
    'author_or_other_reviewer_contacts':0,
    'child_agents':0,
    'selected_source_pins_checked':23,
    'audience_correctness_rows':5,
    'audience_novelty_rows':5,
    'findings':{'medium':['F1 acceptance chronology','F2 positive child answer and budgets','F3 ordinary-rooted convention prominence'],
                'low':['F4 independence heading','F5 once-bound work-model prominence']},
    'source_manifest_pins':{
        'author':'d27ae69ef54c6c03f20c43767fc0b731e5ff96abcfa59f1f426223c77e6a67f5',
        'review':'f85ffa44ccc00d8244608f3b5eef2b32330d9540f3bbe4ab2efa70d7911d1a99'},
    'excludes':'MANIFEST.json itself and MANIFEST.sha256 sidecar',
    'file_count':len(items),
    'files':items,
}
raw=(json.dumps(manifest,indent=2)+'\n').encode()
(OUT/'MANIFEST.json').write_bytes(raw)
sha=hashlib.sha256(raw).hexdigest()
(OUT/'MANIFEST.sha256').write_text(sha+'  MANIFEST.json\n')
# Verify the serialized manifest against each local output; no scientific replay.
stored=json.loads((OUT/'MANIFEST.json').read_text())
assert len(stored['files'])==stored['file_count']
for name,entry in stored['files'].items():
    assert hashlib.sha256((OUT/name).read_bytes()).hexdigest()==entry['sha256']
print(json.dumps({'file_count':len(items),'manifest_sha256':sha},indent=2))
