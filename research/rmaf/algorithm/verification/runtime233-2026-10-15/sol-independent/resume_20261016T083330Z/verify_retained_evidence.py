#!/usr/bin/env python3
"""One-shot retained-evidence audit for this interrupted review continuation.
The existing recheck/adaptation runners already completed; this audits their
saved evidence rather than regenerating it. No reusable toolkit capability
is introduced. SHA identity and receipt consistency confer no replication.
"""
from pathlib import Path
import datetime, gzip, hashlib, json, re, shutil, time

ROOT = Path('/Users/paurel/Documents/ChatGPT/bootscience')
HERE = Path(__file__).resolve().parent
BASE = HERE.parent
PRIOR = BASE / 'postrelease-v2'
PLAN = json.loads((HERE / 'EVIDENCE-AUDIT-PLAN-v1.json').read_text())
start = time.monotonic()
controls = []
contacts = []
seen = {}

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def same(raw, expected):
    if sha(raw) != expected:
        raise ValueError('hash mismatch')

def counts(rows, positive, corruption):
    if any(r['pass'] is not True or r['actual'] != r['expected'] for r in rows):
        raise ValueError('case failed')
    if [sum(r['kind'] == k for r in rows) for k in ('positive', 'corruption')] != [positive, corruption]:
        raise ValueError('case denominator')

def axioms(names):
    if not set(names) <= set(PLAN['allowed_axioms']):
        raise ValueError('unexpected axiom')

def clean(name, fn):
    fn()
    controls.append({'name': name, 'outcome': 'clean passed'})

def corrupt(name, fn):
    try:
        fn()
    except ValueError:
        controls.append({'name': name, 'outcome': 'corruption rejected'})
        return
    raise AssertionError('uncaught control ' + name)

def read(path, digest=None, licensed=False):
    p = path if path.is_absolute() else ROOT / path
    if p in seen:
        raw = seen[p]
    else:
        if p.stat().st_size > PLAN['raw_cap_bytes']:
            raise ValueError('raw cap ' + str(p))
        raw = p.read_bytes()
        seen[p] = raw
    if digest is not None:
        same(raw, digest)
    if licensed:
        key = str(p.relative_to(ROOT))
        if key not in license_index or sha(raw) != license_index[key]:
            raise ValueError('unlicensed or drift ' + key)
        contacts.append({'event': 'LICENSED_IDENTITY_ONLY_NO_BODY_REVIEW', 'path': key,
                         'sha256': sha(raw), 'new_blind_credit': 0})
    return raw

def bounded_log(path, digest):
    raw = read(path, digest)
    data = gzip.decompress(raw)
    if len(data) > PLAN['raw_cap_bytes'] or max(map(len, data.splitlines()), default=0) > PLAN['line_cap_bytes']:
        raise ValueError('log cap')
    return data.decode()

try:
    # Hand-constructed controls are executed before retained real records.
    abc = 'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
    clean('known SHA256 abc', lambda: same(b'abc', abc))
    corrupt('changed abd', lambda: same(b'abd', abc))
    pair = [{'pass': True, 'kind': 'positive', 'actual': 2, 'expected': 2},
            {'pass': True, 'kind': 'corruption', 'actual': False, 'expected': False}]
    clean('synthetic exact denominators', lambda: counts(pair, 1, 1))
    corrupt('synthetic missing case', lambda: counts(pair[:1], 1, 1))
    bad = [dict(pair[0], actual=3), pair[1]]
    corrupt('synthetic failed case', lambda: counts(bad, 1, 1))
    clean('standard synthetic axioms', lambda: axioms(['propext', 'Classical.choice', 'Quot.sound']))
    corrupt('synthetic sorryAx', lambda: axioms(['sorryAx']))
    (HERE / 'EVIDENCE-AUDIT-CONTROLS-v1.json').write_text(json.dumps(controls, indent=2) + '\n')
    if shutil.disk_usage(HERE).free < PLAN['disk_floor_bytes']:
        raise ValueError('disk floor')
    target = Path('research/rmaf/monitoring/resume-20261016T083330Z/runtime-TARGET-v1.json')
    read(target, '2f6cafe200e86fe32bd8a5deb337f2f9b165ac6b7f1a9d823fe745d81ecc9155')
    release_path = Path('research/rmaf/algorithm/verification/runtime233-2026-10-15/ROOT-RELEASE-v2.json')
    release = json.loads(read(release_path, '56f9edbc57396f2c7fe00f72b071ef3e31a5f2f579c738d77cb6c6c2bb9952fe'))
    license_index = {x['path']: x['sha256'] for x in release['licensed_immutable_files']}
    license_index.update({x['manifest']: x['sha256'] for x in release['licensed_packages']})
    if license_index != json.loads(read(PRIOR / 'LICENSE-INDEX-v2.json')):
        raise ValueError('license index differs')
    identities = json.loads(read(HERE / 'PRIOR-IDENTITIES-AT-RESUME.json'))['files']
    if len(identities) != PLAN['expected_prior_files_at_resume']:
        raise ValueError('prior file count')
    for row in identities:
        path = ROOT / row['path']
        read(path, row['sha256'])
        stat = path.stat()
        if [stat.st_size, oct(stat.st_mode & 0o777), stat.st_ino] != [row['bytes'], row['mode'], row['inode']]:
            raise ValueError('prior stat drift ' + row['path'])
    preserved = {}
    for name, expected in [('READY-v1.json', 94), ('postrelease-v1/FINAL-MANIFEST-v1.json', 107)]:
        manifest = BASE / name
        fields = json.loads(read(manifest))['artifacts_sha256']
        if len(fields) != expected:
            raise ValueError('frozen manifest count')
        for name2, digest in fields.items():
            read(manifest.parent / name2, digest)
        preserved[name] = {'sha256': sha(read(manifest)), 'matched_members': len(fields)}
    plan = json.loads(read(PRIOR / 'RECHECK-PLAN-v1.json'))
    expected_modules = {r['module']: r for r in plan['modules']}
    ledger = json.loads(read(PRIOR / 'FAILURE-LEDGER-v2.json'))
    records = []
    summary = []
    printed_reports = []
    for run in ledger['kernel_runs']:
        run_dir = PRIOR / run['path']
        receipt = json.loads(read(run_dir / 'receipt.json', run['receipt_sha256']))
        for rec in receipt['records']:
            item = expected_modules[rec['module']]
            source = read(Path(item['source']), item['source_sha256'], True)
            build = run_dir / item['package']
            if read(build / (item['module'] + '.lean')) != source:
                raise ValueError('selected source differs')
            read(build / (item['module'] + '.olean'), rec['fresh_olean_sha256'])
            if rec['source_sha256'] != item['source_sha256'] or rec['theorems'] != item['theorems']:
                raise ValueError('source/theorem plan mismatch')
            roots = [item['canonical_import_root']] + item.get('additional_import_roots', [])
            canonical = Path(roots[0]) / (item['module'] + '.lean')
            if read(canonical, licensed=True) != source:
                raise ValueError('canonical source differs')
            for pin in rec['reused_pins']:
                read(Path(pin['olean']), pin['olean_sha256'], True)
                read(Path(pin['source']), pin['source_sha256'], True)
            local_outputs = {}
            for kind in ('compile', 'interface'):
                process = rec[kind]
                if process['exit_code'] != 0 or process['timeout'] or process['overflow']:
                    raise ValueError('retained process failure')
                if process['seconds'] >= plan['initial_subprocess_seconds']:
                    raise ValueError('retained process timeout')
                if '-M3072' not in process['command']:
                    raise ValueError('missing calibrated memory cap')
                expected_path = ':'.join([str(build)] + [str(ROOT / root) for root in roots])
                if process['LEAN_PATH'] != expected_path:
                    raise ValueError('package root mismatch')
                local_outputs[kind] = bounded_log(run_dir / process['log'], process['log_sha256'])
            printed = local_outputs['interface']
            reports = re.findall(r"'[^']+' (?:does not depend on any axioms|depends on axioms: \[[^]]*\])", printed)
            names = {n.strip() for group in re.findall(r'depends on axioms: \[([^]]*)\]', printed) for n in group.split(',') if n.strip()}
            axioms(names)
            if reports != rec['axiom_reports'] or len(reports) != len(item['theorems']):
                raise ValueError('axiom report mismatch')
            for th in item['theorems']:
                if th not in printed:
                    raise ValueError('missing theorem print')
            records.append(rec)
            summary.append({'module': item['module'], 'source_sha256': item['source_sha256'],
                            'receipt': str((run_dir / 'receipt.json').relative_to(ROOT)),
                            'receipt_sha256': run['receipt_sha256'], 'roots': roots,
                            'reused_pin_records': len(rec['reused_pins']),
                            'available_pins_are_actual_import_closure': False,
                            'theorems': item['theorems'], 'axioms': sorted(names),
                            'compile_seconds': rec['compile']['seconds'], 'interface_seconds': rec['interface']['seconds']})
            printed_reports.append({'module': item['module'], 'printed': printed})
    if len(records) != PLAN['expected_consumers'] or sum(len(r['theorems']) for r in records) != PLAN['expected_type_axiom_reports']:
        raise ValueError('consumer/report denominator')
    if {r['module'] for r in records} != set(expected_modules):
        raise ValueError('consumer module set')
    adapt = PRIOR / 'adaptation-runs/20261015T215530.502058Z'
    receipt = json.loads(read(adapt / 'receipt.json'))
    fixture_raw = read(PRIOR / 'ADAPTATION-CONTROLS-v2.json', receipt['fixture_sha256'])
    runner_raw = read(PRIOR / 'run_adaptations.py', receipt['runner_sha256'])
    if read(adapt / 'fixture.source.json') != fixture_raw or read(adapt / 'runner.source.py') != runner_raw:
        raise ValueError('retained adapted generator/fixture differs')
    cases = [json.loads(line) for line in read(adapt / 'cases.jsonl').decode().splitlines()]
    counts(cases, PLAN['expected_adaptation_positives'], PLAN['expected_adaptation_corruptions'])
    fixture = json.loads(fixture_raw)
    if [receipt['positives'], receipt['corruption_catches']] != [20, 25]:
        raise ValueError('adaptation receipt denominator')
    sentinels = fixture['source_sentinels']
    source_names = []
    for row in sentinels:
        name = 'research/rmaf/algorithm/universal233/ordinary_dispatch/' + row['file']
        if name not in source_names:
            source_names.append(name)
            original = read(Path(name), licensed=True)
            if read(adapt / ('source-' + str(len(source_names)) + '.lean')) != original:
                raise ValueError('sentinel source snapshot mismatch')
        original = read(Path(name), licensed=True).decode()
        if row['literal'] not in original:
            raise ValueError('missing original sentinel')
    for index, row in enumerate(sentinels, 1):
        changed = bounded_log(adapt / ('omitted-' + str(index) + '.lean.gz'), sha(read(adapt / ('omitted-' + str(index) + '.lean.gz'))))
        if row['literal'] in changed or '[DELIBERATE_OMISSION]' not in changed:
            raise ValueError('missing retained omission corruption')
    all_bytes = sum(p.stat().st_size for p in BASE.rglob('*') if p.is_file())
    gzip_bytes = sum(p.stat().st_size for p in BASE.rglob('*.gz') if p.is_file())
    if gzip_bytes > PLAN['compressed_budget_bytes']:
        raise ValueError('compressed budget')
    result = {'status': 'RETAINED_EVIDENCE_IDENTITY_AND_CONSISTENCY_MATCHED',
              'metadata_controls': len(controls), 'prior_files_unchanged': len(identities),
              'frozen_original_manifests': preserved, 'selected_consumers': summary,
              'selected_type_axiom_reports': 15, 'adapted_positive_cases': 20,
              'adapted_corruption_catches': 25, 'adapted_receipt_sha256': sha(read(adapt / 'receipt.json')),
              'adapted_fixture_sha256': receipt['fixture_sha256'], 'adapted_runner_sha256': receipt['runner_sha256'],
              'all_owned_review_bytes_at_audit': all_bytes, 'all_owned_gzip_bytes': gzip_bytes,
              'elapsed_seconds': time.monotonic() - start, 'new_scientific_replays': 0,
              'new_blind_replication_credit': 0, 'actual_import_closure_reconstructed': False,
              'global_runtime_acceptance': 'OPEN'}
    (HERE / 'RETAINED-EVIDENCE-AUDIT-v1.json').write_text(json.dumps(result, indent=2) + '\n')
    (HERE / 'SELECTED-TYPE-AXIOM-OUTPUT-v1.json').write_text(json.dumps(printed_reports, indent=2) + '\n')
    (HERE / 'IDENTITY-CONTACTS-v1.jsonl').write_text(''.join(json.dumps(r, sort_keys=True) + '\n' for r in contacts))
    print('Retained evidence: 6 selected consumers, 15 printed theorem/axiom reports, 20 adapted results, 25 caught corruptions.')
    print('Original READY94 and phase1 107 members match; 293 prior files retain hashes, modes and inodes.')
    print('Metadata controls 7/7; new scientific replay and blind replication credit 0; global runtime OPEN.')
except BaseException as exc:
    (HERE / 'EVIDENCE-AUDIT-FAILURE-v1.json').write_text(json.dumps({'error': repr(exc), 'controls_completed': controls,
        'seconds': time.monotonic() - start, 'status': 'STOP_FINAL_ACCEPTANCE'}, indent=2) + '\n')
    raise
