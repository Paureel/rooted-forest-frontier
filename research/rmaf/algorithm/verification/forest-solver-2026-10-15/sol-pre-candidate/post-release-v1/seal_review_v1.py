#!/usr/bin/env python3
"""Streaming immutable evidence seal for this review arm only."""
import hashlib
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
PRE = HERE.parent
ROOT = HERE.parents[6]
MANIFEST = HERE / 'FINAL-MANIFEST-v1.json'
READY_SHA = '1c3a10fd1b7da92087e287a18f78c0d831591c343a2c5da0ccc446a694cd3da0'
AUTHOR_SHA = '89937a6f71bceb2dbeb64917b4b805e8f193fa485b00ec28acecdc95d047dcf5'


def sha(path):
    before = path.stat()
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(4 * 1024 * 1024), b''):
            digest.update(chunk)
    after = path.stat()
    assert (before.st_size, before.st_mtime_ns) == (after.st_size, after.st_mtime_ns), str(path) + ' changed during hash'
    return digest.hexdigest()


def load(name):
    return json.loads((HERE / name).read_text())


def prerequisites():
    ready = json.loads((PRE / 'READY-v1.json').read_text())
    assert sha(PRE / 'READY-v1.json') == READY_SHA
    assert len(ready['entries']) == 88
    for row in ready['entries']:
        p = PRE / row['path']
        assert p.stat().st_size == row['size'] and sha(p) == row['sha256'], row['path']
    assert sha(HERE / 'EXACT-AUTHOR-MANIFEST-v3.json') == AUTHOR_SHA
    assert load('ROOT-RELEASE-v1.json')['readiness_sha256'] == READY_SHA
    copied = load('payload-copy-v1.json')
    assert copied['verified'] == 540 and copied['copied'] == 396
    assert copied['excluded_scientific_binaries'] == 144
    for row in copied['entries']:
        if row['copied']:
            p = HERE / 'pinned-payload' / row['path']
            assert p.stat().st_size == row['size'] and sha(p) == row['sha256'], row['path']
    build = load('source-rebuild-v1.json')
    assert build['pilot_passed'] and build['full_passed']
    assert len(build['runs']) == len(build['source_records']) == 143
    for row in build['runs']:
        assert row['returncode'] == 0
        p = HERE / 'isolated-build-v1' / row['module']
        assert sha(p.with_suffix('.lean')) == row['source_sha256'], row['module'] + ' source'
        assert sha(p.with_suffix('.olean')) == row['olean_sha256'], row['module'] + ' fresh olean'
    for row in build['source_records']:
        assert row['original_reconstructed_exactly']
        p = HERE / 'reconstructed-original-source-v1' / row['module']
        assert sha(p.with_suffix('.lean')) == row['sha256'], row['module'] + ' original'
    required = [
        'producer-battery-v1.json', 'producer-battery-v4.json', 'dag-plant-control-v1.json',
        'candidate-origin-batches-v2.json', 'adapter-name-classification-v1.json',
        'natural-name-classification-v1.json', 'PROVENANCE-SCOPE-CHECK-v1.json',
        'actual-check-full-v3.json', 'paid-scheduler-controls-full-v1.json',
        'paid-scheduler-detector-controls-v2.json',
    ]
    for name in required:
        assert load(name)['passed'] is True, name
    assert load('original-adapter-review-v1.json')['full_complete']
    assert load('natural-module-alias-review-v1.json')['complete']
    trace = load('PREMISE-TRACE-v2.json')
    assert len(trace) == 64 and all(not r['unresolved_source_statement'] for r in trace)
    assert not load('REVIEW-RESULT-v4.json')['VERIFIED_CLOSED']
    assert load('seal-hashing-pilot-v1.json')['measured']
    assert load('candidate-origin-batches-v1.json').get('passed') is not True
    return {'original_READY_files': 88, 'fresh_scientific_source_and_olean_pairs': 143,
            'required_positive_receipts': required, 'premise_contract_groups': 64}


def seal():
    assert not MANIFEST.exists(), 'never overwrite existing seal'
    checks = prerequisites()
    files = sorted(p for p in HERE.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p != MANIFEST)
    entries = []
    for p in files:
        entries.append({'path': str(p.relative_to(HERE)), 'size': p.stat().st_size, 'sha256': sha(p)})
    data = {
        'schema': 'independent-scoped-forest-source-review-final-v1',
        'utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
        'owner': '/root/sol_forest_solver_review',
        'status': 'SCOPED_CONFIRMED_WITH_PRINTED_CONDITIONS_AND_PROVENANCE_QUALIFICATIONS',
        'prerelease_READY_sha256': READY_SHA,
        'candidate_v3_manifest_sha256': AUTHOR_SHA,
        'report': 'REVIEW-REPORT-v4.md', 'result': 'REVIEW-RESULT-v4.json',
        'semantic': 'SEMANTIC-REDERIVATION-v2.md', 'origin': 'ORIGIN-RULING-v3.md',
        'work': 'WORK-RULING-v2.md', 'contacts': 'CONTACT-LEDGER-v4.json',
        'integrity_checks': checks,
        'scope': 'OrdinaryIH conditional exactness and LocalBillBound declared bill only',
        'OPEN': ['ordinary dispatcher', 'mutual termination', 'primitive-operation correspondence',
                 'polynomial K', 'scalar bit costs', 'compiled IR/machine semantics', 'global runtime',
                 'smaller global base', 'novelty', 'separate fresh-context frame/referee stage'],
        'VERIFIED_CLOSED': False,
        'preservation': 'all failed/uncredited payloads included; __pycache__ excluded only',
        'entries': entries,
    }
    MANIFEST.write_text(json.dumps(data, indent=2) + '\n')
    for p in files + [MANIFEST]:
        p.chmod(0o444)
    print(json.dumps({'sealed': True, 'payloads': len(entries), 'bytes': sum(r['size'] for r in entries),
                      'manifest_sha256': sha(MANIFEST), 'original_READY_unchanged': True}))


def check():
    data = load(MANIFEST.name)
    assert len(data['entries']) == len({r['path'] for r in data['entries']})
    actual = {str(p.relative_to(HERE)) for p in HERE.rglob('*')
              if p.is_file() and '__pycache__' not in p.parts and p != MANIFEST}
    assert actual == {r['path'] for r in data['entries']}, 'payload name-set drift'
    for row in data['entries']:
        p = HERE / row['path']
        assert p.stat().st_size == row['size'] and sha(p) == row['sha256'], row['path']
        assert p.stat().st_mode & 0o222 == 0, row['path'] + ' writable'
    prerequisites()
    print(json.dumps({'checked': True, 'payloads': len(data['entries']), 'manifest_sha256': sha(MANIFEST),
                      'original_READY_unchanged': True}))


if __name__ == '__main__':
    if sys.argv[1:] == ['seal']:
        seal()
    elif sys.argv[1:] == ['check']:
        check()
    else:
        raise SystemExit('use seal once, then check')
