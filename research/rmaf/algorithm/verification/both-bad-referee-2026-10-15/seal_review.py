"""One-shot local file-inventory seal for the bounded reader review.

No scientific calculation or acceptance test is performed. A later root
editor record must be separately named; preserve this original manifest.
"""
import hashlib
import json
from pathlib import Path
import time

out = Path(__file__).resolve().parent
skip = {'MANIFEST-v1.json','MANIFEST-v1.sha256'}
files = []
for path in sorted(out.iterdir()):
    if path.is_file() and path.name not in skip:
        data = path.read_bytes()
        files.append({'path':path.name,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
manifest = {
    'status':'BOUNDED_READER_REVIEW_WRITER_COMPLETE_ROOT_EDITOR_CONDITION_PENDING',
    'created_unix':time.time(),
    'author_manifest_sha256':'da001ef62039c916cf6db24f61c994094b5b1750f5be9130ddaf512ae5fbe20d',
    'sealed_source_review_FINAL_sha256':'279bb65d6ce96c9d40f85f9cb61af314f42fd89b1950e6ba1ada631611975fb3',
    'report':'REPORT.md',
    'proposed_companion':'COMPANION-PROPOSED-v1.md',
    'source_ledger':'SOURCE-LEDGER-v1.md',
    'contacts':'CONTACTS-v1.json',
    'lint':'LINT-v1.md',
    'retained_initial_drafts':['LINT-PASS1-REPORT.md','LINT-PASS1-COMPANION.md'],
    'reader_inference_only':True,
    'mathematical_replication_increment':0,
    'theorem_replay':False,
    'type_queries_only':11,
    'source_operation_correspondence':'OPEN',
    'full_algorithm_mutual_termination_global_runtime_base_novelty':'OPEN',
    'S11_q4':'original frozen reference failure preserved; no all-controls-pass inference',
    'axiom_summary':'v2 retained; all full lists std3; earlier false two-name explanation superseded',
    'different_editor_condition':'Root must read final rewritten prose and record a separately named result before circulation. Writer self-passes do not satisfy this condition.',
    'future_changes':'Preserve this manifest and sealed files. Any correction or root-editor result must use a new named record/version and its own manifest.',
    'files':files
}
target = out / 'MANIFEST-v1.json'
target.write_text(json.dumps(manifest,indent=2)+'\n')
sha = hashlib.sha256(target.read_bytes()).hexdigest()
(out/'MANIFEST-v1.sha256').write_text(sha+'  MANIFEST-v1.json\n')
print(json.dumps({'files':len(files),'manifest_sha256':sha,'root_editor_condition':'PENDING'}))
