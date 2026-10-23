"""Once-only caller author freeze. Byte checks do not supply independent review."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys
D=Path(__file__).resolve().parent
ROOT=D.parents[4]
O=ROOT/'results/algorithm-universal233-common-split-caller-replay-20261015T134956662297Z'
M=D/'COMMON-SPLIT-CALLER-MANIFEST-v1.json'
H=D/'COMMON-SPLIT-CALLER-MANIFEST-v1.sha256'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def row(p):return {'path':str(p.relative_to(ROOT)),'bytes':p.stat().st_size,'sha256':sha(p)}
def verify():
    assert sha(M)==H.read_text().split()[0]
    d=json.loads(M.read_text())
    for group in ['immutable_files','external_input_pins']:
        for r in d[group]:
            p=ROOT/r['path'];assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],('BYTE_DRIFT',r['path'])
    print('PASS_CALLER_V1_MANIFEST',len(d['immutable_files']),'immutable;',len(d['external_input_pins']),
          'external pins; source applicability/source work/full solver/independent acceptance OPEN')
if '--verify' in sys.argv:
    verify();raise SystemExit(0)
assert len(sys.argv)==1 and not M.exists() and not H.exists(),'ALREADY_FROZEN'
r=json.loads((O/'receipt.json').read_text())
assert r['status']=='PASS_AUTHOR_COMMON_SPLIT_CALLER_SOURCE_BOUND'
assert r['scientific_modules']==len(r['source_inputs'])==173
assert r['axiom_union']==['Classical.choice','Quot.sound','propext']
assert r['false_propositions_rejected']==18 and r['exact_source_adaptations']==0
assert r['runner_self_pin_before_and_after']
assert not r['independent_acceptance'] and not r['full_algorithm'] and not r['runtime_claim']
assert r['all_three_main_milestones']=='OPEN'
for x in r['source_inputs']:
    assert x['sha256']==x['copied_sha256']==sha(ROOT/x['source'])==sha(O/(x['module']+'.lean'))
pin=json.loads((D/'CALLER-AUDIT-CONTROLS-v2.json').read_text())
assert sha(D/'CALLER-AUDIT-CONTROLS-v2.json')==r['detector_pin_sha256']
for p,h in pin['pins'].items():assert sha(ROOT/p)==h,('FINAL_PRE_PIN_DRIFT',p)
assert sha(O/'replay_caller-executed.py')==sha(D/'replay_caller.py')
assert sha(O/'audit_caller-executed.py')==sha(D/'audit_caller.py')
v1=json.loads((D/'CALLER-AUDIT-CONTROLS-v1.json').read_text())
first=ROOT/'results/algorithm-universal233-common-split-caller-replay-20261015T134701293134Z'
assert sha(first/'replay_caller-first.py')==v1['pins'][str((D/'replay_caller.py').relative_to(ROOT))]
for a in r['archives']:
    p=O/a['file'];assert a['roundtrip_match'] and p.stat().st_size==a['bytes'] and sha(p)==a['sha256']
assert len(r['archives'])==173
index=json.loads((O/'producer-records/index.json').read_text())
inventory=json.loads((O/'producer-inventory.json').read_text())
assert not index['rejects'] and len(index['producer_counts'])==173
assert sum(x['count'] for x in index['producer_counts'])==len(inventory)==r['stored_producer_occurrences']
assert len({(x['producer'],x['index']) for x in inventory})==len(inventory)
assert len({x['actual_name'] for x in inventory})==r['resolved_unique_scientific_names']
for name,count in [('FalseControls',5),('GraphFalse',4),('CallerFalse',2),('PaidFalse',2),('OutsideFalse',2),('GuardedFalse',2),('RefusalFalse',1)]:
    assert (O/(name+'.log')).read_text().count('is false')==count
for n in ['missing','duplicate','unresolved','source_byte_plant']:assert r['detector_controls'][n]['caught']
assert r['detector_controls']['coalesced_hostile_at_clean_origin']
byname={}
for x in inventory:byname.setdefault(x['actual_name'],[]).append(x)
coalesced=[]
for name,xs in sorted(byname.items()):
    if len(xs)>1:
        coalesced.append({'actual_name':name,'occurrences':xs,
            'kind_type_body_all_equal':len({(x['kind'],x['type_sha256'],x['body_sha256']) for x in xs})==1})
(D/'COALESCED-OCCURRENCES-v1.json').write_text(json.dumps({'status':'AUTHOR_INVENTORY_NOT_INDEPENDENT_INTERFACE_ADOPTION_REVIEW',
    'stored_occurrences':len(inventory),'resolved_names':len(byname),'coalesced_names':len(coalesced),
    'groups':coalesced,'qualification':'Actual type/body hashes are retained for every stored producer; unequal bodies are not silently described as identical proof replicas.'},indent=2)+'\n')
(D/'FREEZE-CHECKS-v1.json').write_text(json.dumps({'status':'PASS_AUTHOR_CALLER_FREEZE_PACKAGING','utc':datetime.now(timezone.utc).isoformat(),
    'scientific_modules':173,'stored_occurrences':len(inventory),'resolved_names':len(byname),
    'canonical_receipt':str((O/'receipt.json').relative_to(ROOT)),'self_pinned_runner':True,
    'independent_acceptance':False,'source_applicability':'OPEN','source_work':'OPEN','all_three_main_milestones':'OPEN'},indent=2)+'\n')
folders=[D,*sorted((ROOT/'results').glob('algorithm-universal233-common-split-caller-*'))]
files=[]
for folder in folders:
    for p in sorted(folder.rglob('*')):
        if not p.is_file() or p in {M,H} or '__pycache__' in p.parts or p.suffix in {'.olean','.ilean','.pyc'}:continue
        assert not p.is_symlink();files.append(row(p))
assert len({x['path'] for x in files})==len(files)
ext={ROOT/x['source'] for x in r['source_inputs'] if not (ROOT/x['source']).is_relative_to(D)}
ext.update(ROOT/p for p in ['AGENTS.md','bootloops-lean','bootloops-lake','bootloops-python','research/rmaf/lean/lean-toolchain',
 'research/rmaf/algorithm/verification/ORIGIN-AUDIT-SCOPE-AMENDMENT-v1.md',
 'research/rmaf/algorithm/universal233/rule5_common_split/COMMON-SPLIT-GRAPH-MANIFEST-v1.json',
 'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py',
 'research/rmaf/algorithm/universal233/rule5_common_split/replay_graph.py',
 'research/rmaf/algorithm/universal233/rule5_local/RULE5-LOCAL-MANIFEST-v1.json',
 'research/rmaf/algorithm/universal233/query_scheduler/Mass.lean',
 'research/rmaf/sources/baseline/split-or-decompose-v2.txt'])
manifest={'release':'ordinary-common-split-caller-v1','utc':datetime.now(timezone.utc).isoformat(),
    'status':'AUTHOR_GUARDED_SUBROUTINE_KERNEL_CHECKED_SOURCE_APPLICABILITY_AND_WORK_OPEN',
    'canonical_receipt':str((O/'receipt.json').relative_to(ROOT)),
    'theorem':'GuardedExact.runGuarded_answer_exact;actual guarded jobs/literal program output',
    'all_three_main_milestones':'OPEN','full_algorithm':False,'runtime_claim':False,'independent_acceptance':False,
    'counts':{k:r[k] for k in ['scientific_modules','stored_producer_occurrences','resolved_unique_scientific_names','axiom_union']},
    'immutable_files':files,'external_input_pins':[row(p) for p in sorted(ext)],
    'no_write_boundary':'NO-WRITE-BOUNDARY-v1.md','excluded':['.olean','.ilean','.pyc','__pycache__','future source applicability/whole solver packages'],
    'first_open':'Admitted source Rule5.3.1 ->actualSetup/outside1/nonrefusal;fine source-operation bridge/full total mutual solver/runtime.'}
M.write_text(json.dumps(manifest,indent=2)+'\n');H.write_text(sha(M)+'  '+M.name+'\n')
for x in files:
    p=ROOT/x['path'];p.chmod(p.stat().st_mode & ~0o222)
for p in [M,H]:p.chmod(p.stat().st_mode & ~0o222)
verify()
