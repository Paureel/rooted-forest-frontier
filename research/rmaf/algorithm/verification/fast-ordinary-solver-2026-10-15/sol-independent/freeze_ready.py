#!/usr/bin/env python3
"""One-campaign final precontact freeze. Does not read any candidate path.

All inputs are explicit licensed records, own files, or installed runtime files.
An internal alarm bounds this final process without creating a post-manifest
supervisor receipt. Existing frozen readiness files are never overwritten.
"""
import datetime, gzip, hashlib, json, os, pathlib, signal, time

signal.alarm(59)
START=time.monotonic()
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[5]
RUNTIME=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0'

def sha(p):
    h=hashlib.sha256()
    with pathlib.Path(p).open('rb') as f:
        for chunk in iter(lambda:f.read(65536),b''):h.update(chunk)
    return h.hexdigest()

def entry(p):return {'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}

def main():
    ready=HERE/'READY-v1.json';detached=HERE/'READY-v1.sha256'
    if ready.exists() or detached.exists():raise RuntimeError('freeze already exists; use a new explicit version')
    utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
    pins={
      'research/rmaf/algorithm/verification/fast-ordinary-solver-2026-10-15/PRECONTACT-TARGET-v1.json':
        '34460e236c195e0051b7dacda3823eed4f901c0ad160ca99d82fff3adddf7d44',
      'research/rmaf/spec.json':'beac60a68f372b2a561e04ed224b4c2ffc834c95cf5d3a3497bbb44088f9b3f1',
      'research/rmaf/algorithm/TARGET.md':'017d8be230cef2e30eb1f57d078546b7607000fcf409df3bd0083972dbd8f166'}
    for path,pin in pins.items():
        if sha(ROOT/path)!=pin:raise RuntimeError(('licensed pin drift',path))
    if sha(HERE/'FIXTURES-v1.json')!='2b85efc7f393cdea6ec006b68a09beca3048f7355e9f3593b337c99f82293da2':
        raise RuntimeError('hand expectation drift')
    if sha(HERE/'ARTIFACT-LOCK-v1.json')!='ca961c9f3ba7997701155914599ae94adbad44d7ede3882886cf36e92b3dcbe7':
        raise RuntimeError('original artifact lock drift')
    receipts=[];bylabel={};trusted_modules=set();max_line=0
    for p in sorted((HERE/'evidence').glob('*.json')):
        r=json.loads(p.read_text());receipts.append(r)
        if r['label'] in bylabel:raise RuntimeError('duplicate historical label')
        bylabel[r['label']]=r;retained=0
        for shard in r['shards']:
            sp=HERE/shard['path']
            if sha(sp)!=shard['sha256']:raise RuntimeError('evidence shard drift')
            with gzip.open(sp,'rb') as f:
                for line in f:
                    max_line=max(max_line,len(line));retained+=len(line)
                    if len(line)>16*1024**2:raise RuntimeError('actual hard line cap')
                    if retained>64*1024**2:raise RuntimeError('actual hard process cap')
                    try:row=json.loads(line)
                    except (ValueError,UnicodeDecodeError):continue
                    if isinstance(row,dict) and row.get('record')=='external-trust-boundary':
                        trusted_modules.add(row['module'])
        if retained!=r.get('retained_raw_bytes',r['raw_bytes']):raise RuntimeError('retained byte count')
        if r['seconds']>60:raise RuntimeError('actual subprocess time cap')
    def last_result(label):
        r=bylabel[label];shards=r['shards']
        with gzip.open(HERE/shards[-1]['path'],'rt') as f:return json.loads(list(f)[-1])
    sem=last_result('semantic-controls-v2');integrity=last_result('integrity-controls-v3')
    n3=last_result('semantic-pilot-n3');n4=last_result('semantic-pilot-n4')
    if sem['status']!='CONTROL-PASS' or integrity['status']!='INTEGRITY-CONTROL-PASS':raise RuntimeError('control status')
    if integrity['caught_count']!=47 or (n3['ordered_pairs'],n4['ordered_pairs'])!=(9,225):raise RuntimeError('control denominator')
    free=os.statvfs(HERE).f_bavail*os.statvfs(HERE).f_frsize
    compressed=sum(p.stat().st_size for p in HERE.rglob('*.gz'))
    if free<3*1024**3 or compressed>256*1024**2:raise RuntimeError('final resource limit')
    source_contacts=['AGENTS.md','bootloops/tools/README.md','bootloops/tools/gatekeeper/GUIDE.md',
        'bootloops-python','activate.sh']+[
        '.agents/skills/'+s+'/SKILL.md' for s in ('prove-protocol','reading-contract','independence-bookkeeping',
            'planted-truth','timing-discipline','tool-stewardship','acceptance-gate','prose-lint')]
    runtime_sources=['Lean/Declaration.lean','Lean/Expr.lean','Lean/Environment.lean','Lean/Util/Path.lean',
                     'Lean/Util/CollectAxioms.lean','Lean/Level.lean','Lean/Data/KVMap.lean']
    runtime_pins=[entry(RUNTIME/'bin/lean')]+[entry(RUNTIME/'src/lean'/p) for p in runtime_sources]
    for m in sorted(trusted_modules):
        p=RUNTIME/'lib/lean'/pathlib.Path(*m.split('.')).with_suffix('.olean')
        if not p.resolve().is_relative_to(RUNTIME.resolve()):raise RuntimeError('runtime path escape')
        runtime_pins.append(entry(p))
    expected_negative={'stored-producer-dup-ab','stored-producer-dup-ba','guard-raw','guard-line','guard-time','guard-launch'}
    initial_failures={'lean-compile-PAxiom','lean-compile-Producer'}
    failed=[{'label':r['label'],'returncode':r['returncode'],'stop_reason':r['stop_reason'],
             'classification':'expected-negative-control' if r['label'] in expected_negative else
                 'retained-initial-implementation-failure' if r['label'] in initial_failures else 'UNEXPECTED'}
            for r in receipts if r['returncode']!=0 or r['stop_reason'] is not None]
    if any(f['classification']=='UNEXPECTED' for f in failed):raise RuntimeError('unclassified failure')
    ledger={'version':1,'utc':utc,'first_contact':'Pinned PRECONTACT-TARGET-v1.json only; skeleton immediately next',
      'licensed_pin_checks':pins,'supporting_source_contacts':[entry(ROOT/p) for p in source_contacts],
      'runtime_contact_notes':{'source_paths':[str(RUNTIME/'src/lean'/p) for p in runtime_sources],
        'scope':'Declaration portions covering full ConstantInfo payload; Environment import docs; Expr/Level constructors; path discovery; KVMap metadata; CollectAxioms full source. Runtime help/version and toolchain directory names only.'},
      'forbidden_contact':False,'candidate_contact':False,'author_peer_contact':False,'agent_inventory_contact':False,
      'linked_artifact_following':False,'children_created':False,
      'communication':'Only root readiness/scope messages through collaboration tools; no authors or peers.',
      'procedural_deviations':['Initial supporting files were batched and display truncated; all required skills were subsequently read in bounded full excerpts and conclusions recorded. Skeleton still preceded support reads.'],
      'scope_conflicts':['TARGET.md historical author-experiment receipt instruction conflicts with exact PRECONTACT forbiddance; historical receipts were not opened.','Generic bootloops-check was skipped under own-controls/runtime-only contact and write ownership license.'],
      'precontact_adaptations':['noncomputable opaque axiom fixture; typed recursor-rule lambda; explicit Lean package root; complete recursor payload serialization; independent graph malformed-input checks; persistent resource/launch failure receipts. All original failed sources/logs retained.'],
      'postcontact_adaptations':[],'failed_or_stopped_processes':failed,
      'reference_birth':'FIXTURES-v1 hand answers frozen before first execution; exact integers and sets. ARTIFACT-LOCK-v1 is produced-byte integrity only.',
      'independence':'No candidate work authored/read. Graph and partition methods are fresh, share no validity/hull/restriction callbacks, but share author, spec, Python integer/tuple runtime and canonical block ordering. This is cross-method finite calibration, not two-author certification.'}
    (HERE/'CONTACT-AND-FAILURE-LEDGER-v1.json').write_text(json.dumps(ledger,indent=2,sort_keys=True)+'\n')
    owned=[entry(p) for p in sorted(HERE.rglob('*')) if p.is_file() and p not in (ready,detached)]
    result={'version':1,'utc':utc,'status':'READY-PRECONTACT-CONTROLS-ONLY',
      'candidate_contact_permitted':False,'await_root_exact_immutable_whole_solver_release':True,
      'precontact_target_sha256':pins[next(iter(pins))],
      'fixtures_sha256':sha(HERE/'FIXTURES-v1.json'),'artifact_lock_sha256':sha(HERE/'ARTIFACT-LOCK-v1.json'),
      'ownership_root':str(HERE),'owned_files':owned,'owned_file_count':len(owned),
      'licensed_project_pins':pins,'installed_runtime_trust_pins':runtime_pins,
      'compiler_identity':'Lean 4.35.0 arm64-apple-darwin24.6.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc',
      'executed_controls':{'hand_truth_cases':sem['truth_cases'],'partition_validity_cases':sem['validity_cases'],
        'malformed_cases_each_of_two_routes':sem['malformed_cases'],'semantic_named_catches':len(sem['caught']),
        'incomplete_cover_retains_optimum_but_rejected':sem['incomplete_cover_optimum_only_is_blind'],
        'n3':n3,'n4':n4,'integrity_named_catches':integrity['caught_count'],'full_row_audits':integrity['row_audit'],
        'proof_text_policy':'Actual full stored proof expression traversed first; only proof text omitted. Full nonproof/opaque bodies and data retained and structurally walked.',
        'custom_axioms_hidden_unused_sorry':'Actual source gate rejected known negative controls; clean twin admitted.',
        'duplicate_nonproof_both_orders':'Separate values retained; exact duplicate declaration import diagnostic in AB and BA.'},
      'resource_evidence':{'new_compressed_output_bytes':compressed,'compressed_cap_bytes':256*1024**2,
        'live_free_bytes_at_freeze':free,'floor_bytes':3*1024**3,
        'minimum_recorded_free_bytes':min(min(r['free_before'],r['free_after']) for r in receipts),
        'process_receipts':len(receipts),'max_measured_subprocess_seconds':max(r['seconds'] for r in receipts),
        'max_raw_read_bytes_per_process':max(r['raw_bytes'] for r in receipts),'max_retained_line_bytes':max_line,
        'future_stop_threshold_seconds':59,'raw_cap_bytes':64*1024**2,'line_cap_bytes':16*1024**2},
      'not_established':['Candidate algorithm correctness or coverage','Universal ordinary semantic proof','Termination',
        'Candidate source/binary closure','Compiled runtime correspondence','Runtime/exponential base improvement','Novelty'],
      'debt':['Wait for root exact immutable whole-solver release; no self-release.',
        'Arbitrary expression metadata currently refused pending exact encoder calibration.',
        'Installed compiler and Lean/Init/Std are declared trust; direct referenced binaries pinned, full runtime closure unaudited.',
        'Finite n<=4 comparisons are calibration only; no exhaustive n>4 run.',
        'Generic bootloops-check skipped under narrow contact/ownership license.',
        'Same-author two-method checks do not replace fresh external semantic/interface/referee acceptance.'],
      'later_plan':str(HERE/'REPLAY-AND-INTERFACE-PLAN-v1.md'),
      'grading':'READY for later exact licensed review only. No smaller-base or VERIFIED-CLOSED claim.',
      'manifest_self_pin':'Detached READY-v1.sha256; this manifest excludes itself and that detached file from owned_files.'}
    ready.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    detached.write_text(sha(ready)+'  READY-v1.json\n')
    print(json.dumps({'status':result['status'],'ready_sha256':sha(ready),'owned_files':len(owned),
        'compressed_bytes':compressed,'process_receipts':len(receipts),'seconds':time.monotonic()-START},sort_keys=True))

if __name__=='__main__':main()
