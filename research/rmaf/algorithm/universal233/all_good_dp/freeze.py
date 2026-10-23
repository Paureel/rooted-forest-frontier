#!/usr/bin/env python3
"""One-shot source/receipt freeze. Refuses to overwrite an existing manifest."""
from pathlib import Path
import datetime, hashlib, json
D=Path(__file__).resolve().parent
ROOT=D.parents[4]
M=D/'ALL-GOOD-MANIFEST-v1.json'
assert not M.exists(),'Freeze exists; preserve it and create a new version for repairs.'
OUT=ROOT/'results/algorithm-universal233-all-good-20261015T113011Z'
J=json.loads((OUT/'certificate.json').read_text())
assert J['status']=='PASS_AUTHOR_KERNEL_CLOSED_UNVERIFIED_ALL_GOOD'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for row in J['source_inputs']:
    assert sha(ROOT/row['source'])==row['source_sha256'],row['source']
    assert sha(OUT/(row['module']+'.lean'))==row['snapshot_sha256'],row['module']
for p,h in J['input_hashes'].items(): assert sha(ROOT/p)==h,p
(D/'LATEST-REPLAY.txt').write_text(str(OUT)+'\n')
P=D/'preproof-evidence'
P.mkdir(exist_ok=False)
for name in ['RMAF','StateRestriction','StateEmbedding','StatePartition','State','PreControls','FalseControls']:
    for suffix in ['.lean','.log']:
        src=D/'dev/preproof'/(name+suffix)
        (P/src.name).write_bytes(src.read_bytes())
(P/'receipt.json').write_bytes((D/'dev/preproof/receipt.json').read_bytes())
W=D/'WORKFILE.md'
W.write_text(W.read_text()+'\n## Final freeze\n\n'
    'Canonical final receipt: `'+str((OUT/'certificate.json').relative_to(ROOT))+'`.\n'
    'All 79 modules compiled; all 3219 declarations were inventoried by actual\n'
    'origin with only Classical.choice, Quot.sound and propext. The final\n'
    'compiler-call total was '+str(J['compilation_seconds'])+' seconds. Eight authored false\n'
    'claims and every planted audit/source corruption were rejected. The final\n'
    'receipt binds the corrected source-operation counts. Preserved initial\n'
    'control source/log copies are in preproof-evidence/.\n\n'
    'No further writes to any file listed in ALL-GOOD-MANIFEST-v1.json.\n'
    'Author status: CLOSED_UNVERIFIED for the all-good case; fresh review pending.\n'
    'All three main algorithm milestones remain OPEN.\n')
files=[p for p in D.iterdir() if p.is_file() and p!=M]
files+=list(P.iterdir())
files+=[p for p in OUT.iterdir() if p.is_file() and p.suffix not in ['.olean','.ilean']]
rows=[{'path':str(p.relative_to(ROOT)),'sha256':sha(p)} for p in sorted(files)]
manifest={'version':1,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'status':'FROZEN_AUTHOR_EXACT_ALL_GOOD_CASE_CLOSED_UNVERIFIED',
 'canonical_receipt':str((OUT/'certificate.json').relative_to(ROOT)),
 'all_three_main_milestones':'OPEN','fresh_nonauthor_acceptance':False,'novelty':'NO_CLAIM',
 'first_unproved_subcase_theorem':None,
 'acceptance_remaining':J['acceptance_remaining'],
 'module_origin_total':J['module_origin_total'],'source_modules':len(J['positive_order']),
 'axiom_union_observed':J['axiom_union_observed'],
 'source_cost_qualification':J['source_cost_qualification'],
 'no_write_boundary':'Every listed source, document, pre-proof evidence and canonical receipt is immutable. Replays write new results directories only. Repairs require a new version.',
 'excluded_mutable_development':'dev/, __pycache__/, and derived olean/ilean files',
 'immutable_files':rows}
M.write_text(json.dumps(manifest,indent=2)+'\n')
for row in rows: assert sha(ROOT/row['path'])==row['sha256'],row['path']
print(json.dumps({'manifest':str(M.relative_to(ROOT)),'manifest_sha256':sha(M),
                 'immutable_files':len(rows),'canonical_receipt':manifest['canonical_receipt']},indent=2))
