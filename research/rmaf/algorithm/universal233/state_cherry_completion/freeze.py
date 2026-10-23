#!/usr/bin/env python3
"""One-shot author release pin writer/verifier; no toolkit capability added.

The existing state manifest/replay pattern is reused for this problem-local
freeze. An existing manifest is verified without rewriting it.
"""
from pathlib import Path
import datetime,hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
MANIFEST=HERE/'CHERRY-MANIFEST-v1.json'
CANON=ROOT/'results/algorithm-universal233-state-cherry-20261015T101755Z'
SUMMARY=ROOT/'research/rmaf/results/algorithm-universal233-state-cherry-20261015T101755Z.json'
STATE=HERE.parent/'state_reductions/STATE-MANIFEST-v1.json'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def verify(record):
    for f in record['immutable_files']:
        assert sha(ROOT/f['path'])==f['sha256'],'changed frozen file: '+f['path']
    assert sha(STATE)==record['dependency_manifest_sha256']
    for f in json.loads(STATE.read_text())['immutable_files']:
        assert sha(ROOT/f['path'])==f['sha256'],'changed state dependency: '+f['path']
if MANIFEST.exists():
    record=json.loads(MANIFEST.read_text())
    verify(record)
    print(json.dumps({'status':'PASS_EXISTING_FREEZE','files':len(record['immutable_files'])}))
    raise SystemExit(0)
cert=json.loads((CANON/'certificate.json').read_text())
assert cert['status']=='PASS_AUTHOR_KERNEL_REPLAY_COMPLETED_COMMON_CHERRY'
assert cert['module_origin_total']==702 and len(cert['module_origin_counts'])==23
assert cert['first_unproved_common_cherry_consumer'] is None
assert cert['all_three_main_milestones']=='OPEN'
assert cert['fresh_nonauthor_acceptance'] is False
for rel,h in cert['input_hashes'].items(): assert sha(ROOT/rel)==h,'changed author source: '+rel
files=[p for p in HERE.iterdir() if p.is_file() and p.name not in {'LATEST-REPLAY.txt','CHERRY-MANIFEST-v1.json'}]
files += [p for p in CANON.iterdir() if p.is_file() and p.suffix not in {'.olean','.ilean'}]
files += [SUMMARY]
record={'version':1,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'status':'FROZEN AUTHOR completed common-cherry proof; fresh nonauthor review pending',
        'grade':'CLOSED_UNVERIFIED','full_algorithm_proved':False,
        'all_three_main_milestones':'OPEN','fresh_nonauthor_acceptance':False,
        'canonical_receipt':str((CANON/'certificate.json').relative_to(ROOT)),
        'dependency_manifest':str(STATE.relative_to(ROOT)),
        'dependency_manifest_sha256':sha(STATE),
        'completed':'exact endpoint embeddings; no-larger literal state agreement; literal contract/expand; fresh partitions; exact additional cost; every-budget decision equivalence; exact current-label decrease',
        'first_unproved_mathematical_consumer':None,
        'next_acceptance':'fresh nonauthor proof, statement, source, and interface review',
        'no_further_writes':True,
        'excluded_mutable_development':['state_cherry_completion/preproof/','olean/ilean cache files','state_cherry_completion/LATEST-REPLAY.txt'],
        'immutable_files':[{'path':str(p.relative_to(ROOT)),'sha256':sha(p)} for p in sorted(set(files))]}
verify(record)
MANIFEST.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':'PASS_NEW_AUTHOR_FREEZE','files':len(record['immutable_files']),
                  'manifest':str(MANIFEST.relative_to(ROOT)),'manifest_sha256':sha(MANIFEST)},indent=2))
