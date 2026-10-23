"""Once-only byte freeze of the graph author checkpoint; no independent credit."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, sys

D=Path(__file__).resolve().parent
ROOT=D.parents[4]
M=D/'COMMON-SPLIT-GRAPH-MANIFEST-v1.json'
H=D/'COMMON-SPLIT-GRAPH-MANIFEST-v1.sha256'
R=ROOT/'results/algorithm-universal233-common-split-graph-20261015T132015611066Z'

def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()

def entry(p):return {'path':str(p.relative_to(ROOT)),'bytes':p.stat().st_size,'sha256':sha(p)}

def verify():
    assert sha(M)==H.read_text().split()[0], 'MANIFEST_HASH'
    d=json.loads(M.read_text())
    for group in ['immutable_files','external_input_pins']:
        for r in d[group]:
            p=ROOT/r['path']
            assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'], ('BYTE_DRIFT',r['path'])
    print('PASS_GRAPH_V1_MANIFEST',len(d['immutable_files']),'immutable;',len(d['external_input_pins']),
          'external pins; independent acceptance/full solver/runtime OPEN')

if '--verify' in sys.argv:
    verify();raise SystemExit(0)
assert len(sys.argv)==1 and not M.exists() and not H.exists(), 'ALREADY_FROZEN'
r=json.loads((R/'receipt.json').read_text())
assert r['status']=='PASS_AUTHOR_COMMON_SPLIT_GRAPH_SOURCE_BOUND'
assert r['scientific_modules']==len(r['source_inputs'])==151
assert r['stored_producer_occurrences']==4238 and r['resolved_unique_scientific_names']==4210
assert r['axiom_union']==['Classical.choice','Quot.sound','propext']
assert r['false_propositions_rejected']==9 and r['exact_source_adaptations']==0
assert not r['independent_acceptance'] and not r['full_algorithm'] and not r['runtime_claim']
assert r['all_three_main_milestones']=='OPEN'
for row in r['source_inputs']:
    assert row['sha256']==row['copied_sha256']==sha(ROOT/row['source'])==sha(R/(row['module']+'.lean'))
pin=json.loads((D/'GRAPH-AUDIT-CONTROLS-v1.json').read_text())
assert sha(D/'GRAPH-AUDIT-CONTROLS-v1.json')==r['detector_pin_sha256']
for p,h in pin['pins'].items():assert sha(ROOT/p)==h,('DETECTOR_PIN',p)
assert all(a['roundtrip_match'] and sha(R/a['file'])==a['sha256'] and
           (R/a['file']).stat().st_size==a['bytes'] for a in r['archives'])
assert len(r['archives'])==151
idx=json.loads((R/'producer-records/index.json').read_text())
assert not idx['rejects'] and sum(c['count'] for c in idx['producer_counts'])==4238
inventory=json.loads((R/'producer-inventory.json').read_text())
assert len(inventory)==4238 and len({(x['producer'],x['index']) for x in inventory})==4238
assert (R/'FalseControls.log').read_text().count('is false')==5
assert (R/'GraphFalse.log').read_text().count('is false')==4
bad={'FalseControls','GraphFalse','DetectorHostileAB','DetectorHostileBA','DetectorUnused'}
assert all(x['exit']==(1 if x['module'] in bad else 0) for x in r['runs'])
assert r['detector_controls']['coalesced_hostile_at_clean_origin']
for name in ['missing','duplicate','unresolved','source_byte_plant']:
    assert r['detector_controls'][name]['caught']
for p in json.loads((D/'PREPROOF-PIN-v1.json').read_text())['files']:
    assert sha(ROOT/p['path'])==p['sha256'],('PREPROOF_PIN',p['path'])

checks={'status':'PASS_AUTHOR_GRAPH_FREEZE_PACKAGING','utc':datetime.now(timezone.utc).isoformat(),
        'canonical':str(R.relative_to(ROOT)),
        'scientific_sources_exact':151,'stored_producer_occurrences':4238,'resolved_names':4210,
        'source_runtime_claim':False,'independent_acceptance':False,
        'runner_sha256_at_freeze':sha(D/'replay_graph.py'),
        'runner_preexecution_self_pin':False,
        'runner_qualification':'Scientific sources/detector inputs were pre-pinned; runner frozen after execution.',
        'all_three_main_milestones':'OPEN'}
(D/'FREEZE-CHECKS-GRAPH-v1.json').write_text(json.dumps(checks,indent=2)+'\n')
folders=[D,*sorted((ROOT/'results').glob('algorithm-universal233-common-split-*'))]
files=[]
for folder in folders:
    for p in sorted(folder.rglob('*')):
        if not p.is_file() or p in {M,H} or '__pycache__' in p.parts or p.suffix in {'.olean','.ilean','.pyc'}:continue
        assert not p.is_symlink()
        files.append(entry(p))
assert len({x['path'] for x in files})==len(files)
ext={ROOT/x['source'] for x in r['source_inputs'] if not (ROOT/x['source']).is_relative_to(D)}
ext.update(ROOT/p for p in ['AGENTS.md','bootloops-lean','bootloops-lake','bootloops-python',
    'research/rmaf/lean/lean-toolchain','research/rmaf/sources/baseline/split-or-decompose-v2.txt',
    'research/rmaf/algorithm/verification/ORIGIN-AUDIT-SCOPE-AMENDMENT-v1.md',
    'research/rmaf/algorithm/universal233/rule4/audit_support.py',
    'research/rmaf/algorithm/universal233/rule4/replay.py',
    'research/rmaf/algorithm/universal233/final_cut_recovery/Permutations.lean'])
manifest={'release':'ordinary-common-split-graph-v1','utc':datetime.now(timezone.utc).isoformat(),
    'status':'AUTHOR_GRAPH_KERNEL_CHECKED_FRESH_NONAUTHOR_ACCEPTANCE_OPEN',
    'canonical_receipt':str((R/'receipt.json').relative_to(ROOT)),
    'theorem':'DerivedMinimum.common_split_derived_minimum',
    'all_three_main_milestones':'OPEN','full_algorithm':False,'runtime_claim':False,
    'counts':{k:r[k] for k in ['scientific_modules','stored_producer_occurrences','resolved_unique_scientific_names','axiom_union']},
    'immutable_files':files,'external_input_pins':[entry(p) for p in sorted(ext)],
    'no_write_boundary':'NO-WRITE-BOUNDARY-GRAPH-v1.md',
    'excluded':['.olean','.ilean','.pyc','__pycache__','future rule5_common_split_caller/'],
    'first_open':'Actual Rule5.3.1 applicability/outside minimum1, actual pretest/paid q-1 calls/literal reconstruction/source runtime.'}
M.write_text(json.dumps(manifest,indent=2)+'\n')
H.write_text(sha(M)+'  '+M.name+'\n')
for x in files:
    p=ROOT/x['path'];p.chmod(p.stat().st_mode & ~0o222)
for p in [M,H]:p.chmod(p.stat().st_mode & ~0o222)
verify()
