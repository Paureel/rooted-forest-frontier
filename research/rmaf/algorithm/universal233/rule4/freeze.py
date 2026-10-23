#!/usr/bin/env python3
"""Freeze once, then verify the Rule4 author release without changing it.

This is byte-integrity/receipt validation, not independent scientific review.
The canonical mathematical and producer controls ran before this packaging.
"""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess
import sys

D = Path(__file__).resolve().parent
ROOT = D.parents[4]
MANIFEST = D / 'RULE4-MANIFEST-v1.json'
COMPANION = D / 'RULE4-MANIFEST-v1.sha256'
CANONICAL = ROOT / 'results/algorithm-universal233-rule4-replay-20261015T124859Z'
CONTROL = ROOT / 'results/algorithm-universal233-rule4-controls-20261015T115429Z'


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as source:
        while block := source.read(1024 * 1024):
            h.update(block)
    return h.hexdigest()


def relative(path):
    return str(path.relative_to(ROOT))


def load(path):
    return json.loads(path.read_text())


def verify():
    expected = COMPANION.read_text().split()[0]
    assert digest(MANIFEST) == expected, 'MANIFEST_HASH_MISMATCH'
    data = load(MANIFEST)
    for group in ['immutable_files', 'external_input_pins']:
        for row in data[group]:
            path = ROOT / row['path']
            assert path.is_file(), ('MISSING_FILE', row['path'])
            assert path.stat().st_size == row['bytes'], ('SIZE_MISMATCH', row['path'])
            assert digest(path) == row['sha256'], ('FILE_HASH_MISMATCH', row['path'])
    print('PASS_RULE4_V1_MANIFEST_BYTES', len(data['immutable_files']),
          'immutable files;', len(data['external_input_pins']),
          'external input pins; independent acceptance OPEN.')
    return data


if '--verify' in sys.argv:
    verify()
    raise SystemExit(0)
assert len(sys.argv) == 1, 'Only --verify is supported after freeze.'
assert not MANIFEST.exists() and not COMPANION.exists(), 'RELEASE_ALREADY_FROZEN'

r = load(CANONICAL / 'receipt.json')
c = load(CONTROL / 'receipt.json')
assert r['status'] == 'PASS_AUTHOR_RULE4_SOURCE_BOUND_REPLAY'
assert r['positive_source_modules'] == len(r['source_inputs']) == 95
assert len(r['producer_counts']) == 95
assert sum(x['count'] for x in r['producer_counts']) == r['producer_occurrences'] == 3513
assert r['resolved_unique_scientific_names'] == 3487
assert r['axiom_union'] == ['Classical.choice', 'Quot.sound', 'propext']
assert not r['independent_acceptance'] and r['all_three_main_milestones'] == 'OPEN'
assert r['false_propositions_rejected'] == 5 and r['source_body_adaptations'] == 0
assert r['source_pin_corruption_caught']
assert r['source_pin_plant_rejection'].startswith('SOURCE_PIN_MISMATCH: ')
assert 'SOURCE_PIN_MISMATCH' in (D / 'replay.py').read_text()
for file, key in [('replay.py', 'runner_sha256'),
                  ('audit_support.py', 'audit_support_sha256'),
                  ('SOURCE-INPUTS-v1.json', 'source_ledger_sha256')]:
    assert digest(D / file) == r[key], ('CANONICAL_INSTRUMENT_DRIFT', file)
for row in r['source_inputs']:
    assert row['adaptation'] == 'none; exact bytes'
    assert row['sha256'] == row['compiled_sha256']
    assert digest(ROOT / row['source']) == row['sha256'], ('SOURCE_DRIFT', row['module'])
    assert digest(CANONICAL / (row['module'] + '.lean')) == row['sha256']
assert (CANONICAL / 'Rule4False.log').read_text().count('is false') == 5
assert '(43300 : Rat)/54289' in (CANONICAL / 'Rule4Controls.log').read_text()
expected_failures = {'Rule4False', 'DetectorBadAB', 'DetectorBadBA'}
for row in r['runs']:
    expected = 1 if row['module'] in expected_failures else 0
    assert row['exit'] == expected, ('UNEXPECTED_BUILD_STATUS', row['module'])
assert c['status'] == 'PASS_PREPROOF_ACTUAL_RULE4_CONTROLS'
assert c['positive_actual_fixtures'] == 2
assert c['conditional_callback_budget_tests'] == 10
assert c['false_claims_rejected'] == 5 and c['corruptions_rejected'] == 6
assert digest(D / 'CONTROLS-v1.json') == c['pin_sha256']
assert digest(D / 'rule4.py') == c['source_sha256']

pin = load(D / 'AUDIT-CONTROLS-v1.json')
for name, expected in pin['pins'].items():
    assert digest(ROOT / name) == expected, ('DETECTOR_SOURCE_DRIFT', name)
assert digest(D / 'audit_support.py') == pin['instrument']['sha256']
clean = load(CANONICAL / 'DetectorClean.json')
twins = [x for x in clean['occurrences'] if x['actual_name'] == 'DetectorShared.shared']
assert len(twins) == 2 and {x['producer'] for x in twins} == {'DetectorAlpha', 'DetectorBeta'}
assert twins[0]['type'] == twins[1]['type'] and twins[0]['body'] == twins[1]['body']
assert all(x['kind'] == 'theorem' and x['has_body'] for x in twins)
for name in ['DetectorBadAB', 'DetectorBadBA']:
    data = load(CANONICAL / (name + '.json'))
    hostile = [x for x in data['occurrences']
               if x['producer'] == 'DetectorHostile' and x['actual_name'] == 'DetectorShared.shared']
    assert len(hostile) == 1 and hostile[0]['kind'] == 'axiom'
    assert hostile[0]['type'] == twins[0]['type'] and not hostile[0]['has_body']
    assert any(x['producer'] == 'DetectorHostile' and
               x['actual_name'] == 'hostileOwnClean' and x['kind'] == 'theorem'
               for x in data['occurrences'])
assert r['detector_control_results']['coalesced_hostile_caught']
for name in ['missing_occurrence', 'duplicate_occurrence']:
    assert r['detector_control_results'][name]['caught']

storage = []
for folder in sorted((ROOT / 'results').glob('algorithm-universal233-rule4-replay-*')):
    row = load(folder / 'occurrence-storage.json')
    archive = folder / row['stored_archive']
    assert row['lossless_roundtrip_sha256_match']
    assert archive.stat().st_size == row['archive_bytes']
    assert digest(archive) == row['archive_sha256']
    assert row['source_bytes'] > 0 and not (folder / row['source_name']).exists()
    storage.append({'receipt': relative(folder), **row})

versions = {}
for wrapper in ['bootloops-lean', 'bootloops-lake']:
    proc = subprocess.run([str(ROOT / wrapper), '--version'], cwd=ROOT,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=20)
    assert proc.returncode == 0, ('RUNTIME_VERSION_FAILURE', wrapper)
    versions[wrapper] = proc.stdout.strip()

checks = {
    'status': 'PASS_AUTHOR_RELEASE_PACKAGING_CHECKS',
    'time': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'canonical_receipt': relative(CANONICAL / 'receipt.json'),
    'positive_source_modules': r['positive_source_modules'],
    'producer_occurrences': r['producer_occurrences'],
    'resolved_unique_scientific_names': r['resolved_unique_scientific_names'],
    'clean_twins_actual_type_and_body_equal': True,
    'hostile_actual_type_matches_clean': True,
    'hostile_own_clean_declaration_present_both_orders': True,
    'canonical_sources_and_instruments_match_recorded_hashes': True,
    'lossless_occurrence_archives_match_roundtrip_recorded_hashes': True,
    'runtime_versions': versions,
    'independent_acceptance': False,
    'all_three_main_milestones': 'OPEN',
    'interpretation': 'Packaging checks complement the executed canonical source-bound receipt; they are not an independent proof audit.'
}
(D / 'FREEZE-CHECKS-v1.json').write_text(json.dumps(checks, indent=2) + '\n')

folders = [D, *sorted((ROOT / 'results').glob('algorithm-universal233-rule4-*'))]
files = []
for folder in folders:
    for path in sorted(folder.rglob('*')):
        if not path.is_file() or path.name in {MANIFEST.name, COMPANION.name}:
            continue
        if '__pycache__' in path.parts or path.suffix in {'.olean', '.ilean', '.pyc'}:
            continue
        assert not path.is_symlink(), ('UNSUPPORTED_SYMLINK', str(path))
        files.append({'path': relative(path), 'bytes': path.stat().st_size, 'sha256': digest(path)})
assert len({x['path'] for x in files}) == len(files), 'DUPLICATE_MANIFEST_PATH'
external = {ROOT / x['source'] for x in r['source_inputs'] if not (ROOT / x['source']).is_relative_to(D)}
external.update(ROOT / p for p in [
    'research/rmaf/sources/baseline/split-or-decompose-v2.txt',
    'research/rmaf/algorithm/verification/ORIGIN-AUDIT-SCOPE-AMENDMENT-v1.md',
    'research/rmaf/lean/lean-toolchain', 'bootloops-lean', 'bootloops-lake', 'bootloops-python'])
external.update(ROOT / p for p in pin['pins'] if not (ROOT / p).is_relative_to(D))
data = {
    'release': 'original-rooted-rule4-v1',
    'status': 'AUTHOR_KERNEL_COMPLETE_INDEPENDENT_ACCEPTANCE_OPEN',
    'all_three_main_milestones': 'OPEN',
    'time': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'canonical_receipt': relative(CANONICAL / 'receipt.json'),
    'preproof_control_receipt': relative(CONTROL / 'receipt.json'),
    'canonical_counts': {k: r[k] for k in ['positive_source_modules', 'producer_occurrences',
                                         'resolved_unique_scientific_names', 'axiom_union']},
    'storage': storage,
    'immutable_files': files,
    'external_input_pins': [{'path': relative(p), 'bytes': p.stat().st_size, 'sha256': digest(p)}
                            for p in sorted(external)],
    'excluded_derived_extensions': ['.olean', '.ilean', '.pyc'],
    'excluded_derived_directories': ['__pycache__'],
    'no_write_boundary': 'NO-WRITE-BOUNDARY.md; repairs require a new version and new result evidence.',
    'remaining': 'Fresh nonauthor semantic/interface/source-cost/prose acceptance; full recursive solver/global recurrence/smaller base/novelty OPEN.'
}
MANIFEST.write_text(json.dumps(data, indent=2) + '\n')
COMPANION.write_text(digest(MANIFEST) + '  ' + MANIFEST.name + '\n')
for row in files:
    path = ROOT / row['path']
    path.chmod(path.stat().st_mode & ~0o222)
MANIFEST.chmod(MANIFEST.stat().st_mode & ~0o222)
COMPANION.chmod(COMPANION.stat().st_mode & ~0o222)
verify()
