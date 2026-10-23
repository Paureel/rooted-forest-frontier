#!/usr/bin/env python3
"""One-shot seal for the local fresh-context framing review.

No shared toolkit was changed. Uses standard SHA-256 to bind local review files
and recheck the already selected frozen inputs; no scientific replay is performed.
"""
import hashlib
import json
from pathlib import Path

BASE=Path(__file__).resolve().parent
ROOT=BASE.parents[4]
OUT=BASE/'REVIEW-MANIFEST-v1.json'
SUM=BASE/'REVIEW-MANIFEST-v1.sha256'
assert not OUT.exists() and not SUM.exists(), 'sealed review already exists'
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
evidence=json.loads((BASE/'BOUNDED-EVIDENCE-RECEIPT.json').read_text())
for rel,h in evidence['selected_hashes'].items():
    assert sha(ROOT/rel)==h, rel
excluded={OUT.name,SUM.name}
files={str(p.relative_to(BASE)):{'sha256':sha(p),'bytes':p.stat().st_size}
       for p in sorted(BASE.rglob('*')) if p.is_file() and p.name not in excluded}
manifest={
 'status':'FRESH-CONTEXT-FRAMING-REVIEW-WITH-PROPOSED-ERRATUM',
 'scope':'sealed-report framing and 23 named file/type/receipt checks only',
 'findings':{'F1':'MEDIUM','F2':'MEDIUM','F3':'MEDIUM','F4':'LOW-OPTIONAL'},
 'frozen_files_edited':False,'proposed_diff_applied':False,
 'new_Lean_execution':False,'new_mathematical_replications':0,
 'author_or_child_or_other_reviewer_contacts':0,
 'different_editor_lint_condition':'UNMET: same reviewer, TARGET forbids reviewer contact',
 'main_milestones':{'complete_solver':'OPEN','global_faster_runtime':'OPEN','novelty':'OPEN'},
 'named_consumers':{'MINIMUM-SELECTION':'OPEN','MAIN-CALL-ONCE':'OPEN','GLOBAL-RECURRENCE':'OPEN'},
 'source_manifests':{
  'author':'95569c46912bff25f74cd01174bc51a934e7395524922271e6de4538fbdc4fb3',
  'reviewer':'4699c40246839ad60e860f3ae280e6b159cb7e3a00e0383d0b5359b9780bbc71'},
 'file_count':len(files),'files':files,
 'manifest_rule':'self and detached sha256 excluded to avoid self-reference; no output files may change after sealing'}
OUT.write_text(json.dumps(manifest,indent=2)+'\n')
SUM.write_text(sha(OUT)+'  '+OUT.name+'\n')
assert all(sha(BASE/p)==d['sha256'] for p,d in files.items())
print(json.dumps({'file_count':len(files),'manifest_sha256':sha(OUT),
                  'selected_frozen_files_unchanged':len(evidence['selected_hashes'])}))
