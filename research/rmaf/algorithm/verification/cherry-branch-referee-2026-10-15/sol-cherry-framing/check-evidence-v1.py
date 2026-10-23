#!/usr/bin/env python3
"""One-shot document identity/count/quote check; no proof or scientific replay.

The toolkit index and emitall guide were consulted. Emitall does not combine
manifest payload verification with line-range quote receipts. This script is
intentionally local to this review. METHOD-v1.md defines failure in advance.
"""
import hashlib
import json
import time
from pathlib import Path

ROOT = Path('/Users/paurel/Documents/ChatGPT/bootscience')
OUT = Path(__file__).resolve().parent
started = time.perf_counter()
sha = lambda data: hashlib.sha256(data).hexdigest()

def matches(data, row):
    return len(data) == row['bytes'] and sha(data) == row['sha256']

def quoted(text, quote):
    return quote in text

fixture = b'clean local document fixture\n'
clean = {'bytes': len(fixture), 'sha256': sha(fixture)}
controls = {
    'clean_row': matches(fixture, clean),
    'changed_bytes_rejected': not matches(fixture+b'x', clean),
    'changed_hash_rejected': not matches(fixture, {**clean, 'sha256': '0'*64}),
    'changed_size_rejected': not matches(fixture, {**clean, 'bytes': len(fixture)+1}),
    'clean_quote': quoted('clean quotation', 'quotation'),
    'changed_quote_rejected': not quoted('clean quotation', 'altered quotation'),
}
assert all(controls.values()), controls

manifest_specs = [
    ('author', 'research/rmaf/algorithm/universal233/cherry_branching/CHERRY-BRANCH-MANIFEST-v1.json',
     'immutable_files', '5ffb1fa6e9810485f60ced7e4e5d9cccc0f915fa95e9ba9e4998550b17eebe5d', 290),
    ('sealed_review', 'research/rmaf/algorithm/verification/cherry-branch-2026-10-15/sol-main-necessity/postrelease-v1/FINAL-MANIFEST-v1.json',
     'files', '64482ada09e73817784e8842f746724bd99ffdc2363b73cb8c12a271c670e45e', 289),
]
manifests = []
manifest_paths = set()
for label, path, key, expected, count in manifest_specs:
    data = (ROOT/path).read_bytes()
    assert sha(data) == expected, (label, 'manifest pin')
    rows = json.loads(data)[key]
    assert len(rows) == count, (label, 'row count')
    assert len({r['path'] for r in rows}) == count, (label, 'duplicate path')
    for row in rows:
        assert matches((ROOT/row['path']).read_bytes(), row), row['path']
        manifest_paths.add(row['path'])
    manifests.append({'label': label, 'path': path, 'sha256': sha(data),
                      'matching_payloads': len(rows), 'bytes': len(data)})

spec = json.loads((OUT/'evidence-spec-v1.json').read_text())
inputs = {}
for label, path in spec['sources'].items():
    data = (ROOT/path).read_bytes()
    inputs[label] = {'path': path, 'absolute_path': str(ROOT/path),
                     'bytes': len(data), 'sha256': sha(data),
                     'manifest_payload': path in manifest_paths}
quotes = []
for quote in spec['quotations']:
    path = spec['sources'][quote['source']]
    lines = (ROOT/path).read_text().splitlines()
    excerpt = '\n'.join(lines[quote['start']-1:quote['end']])
    assert quoted(excerpt, quote['text']), quote['id']
    quotes.append({**quote, 'path': path, 'line_excerpt': excerpt, 'exact': True})

def receipt(alias):
    return json.loads((ROOT/spec['sources'][alias]).read_text())

gate, summary, coalesced, readout, mutation, pilot, remaining, raw = map(
    receipt, ['J1','J2','J3','J4','J5','J6','J7','J8'])
producers = raw['producers']
assert len(producers) == 71
assert sum(p['count'] > 0 for p in producers) == 70
assert [(p['module'], p['count']) for p in producers if not p['count']] == [('Interfaces', 0)]
assert sum(p['count'] for p in producers) == 2659
assert gate['modules'] == 71 and gate['nonempty_producers'] == 70
assert gate['stored_occurrences'] == summary['occurrences'] == coalesced['stored_occurrences'] == 2659
assert gate['unique_resolved_names'] == summary['unique_names'] == coalesced['resolved_unique_names'] == 2638
assert len(coalesced['groups']) == coalesced['coalesced_names'] == 18
assert sum(len(g['occurrences'])-1 for g in coalesced['groups']) == coalesced['coalesced_extra_occurrences'] == 2659-2638 == 21
assert len(gate['controls']) == 18
assert all(c.get('pass', c.get('reject', False)) for c in gate['controls'])
assert gate['instrument_sha256'] == summary['instrument_sha256']
assert summary['unchanged_instrument'] and summary['scientific_oleans_copied'] == 0
assert summary['direct_axioms'] == summary['missing_refs'] == []
assert summary['axioms'] == ['Classical.choice','Quot.sound','propext']
assert len(readout['cases']) == 7 and readout['priority_cases'] == 5
assert readout['source_states_checked'] == 21 and readout['actual_child_calls'] == 12
assert readout['expected_files_unchanged']
assert len(mutation['mutations']) == 6 and mutation['clean_twin']
assert all(m['caught'] and m['returncode'] == 1 for m in mutation['mutations'])
builds = pilot['records'] + remaining['records']
assert len(builds) == len({r['module'] for r in builds}) == 71
for row in builds:
    assert row['returncode'] == 0
    source, olean = Path(row['command'][-1]), Path(row['command'][row['command'].index('-o')+1])
    assert sha(source.read_bytes()) == row['source_sha256']
    assert sha(olean.read_bytes()) == row['olean_sha256']

result = {
    'scope': 'document identity, quoted locations and retained receipt arithmetic only',
    'controls_before_real_inputs': controls,
    'manifests': manifests,
    'inputs': inputs,
    'quotations': quotes,
    'retained_receipt_checks': {
        'build_records': len(builds), 'zero_declaration_module': 'Interfaces',
        'module_headers': len(producers), 'nonempty_producers': 70,
        'stored_occurrences': 2659, 'resolved_names': 2638,
        'coalesced_names': 18, 'extra_occurrences': 21,
        'standard_axioms': summary['axioms'],
        'zero_schema_controls': len(gate['controls']),
        'unchanged_detector_hash_in_receipts': gate['instrument_sha256'],
        'tree_readouts': len(readout['cases']), 'priority_readouts': 5,
        'materialized_states': 21, 'mock_calls': 12,
        'postcontact_comparator_mutations': len(mutation['mutations']),
        'build_source_and_olean_hashes_match_retained_records': True,
    },
    'new_mathematical_replications': 0,
    'new_lean_invocations': 0,
    'seconds': time.perf_counter()-started,
}
(OUT/'EVIDENCE-LEDGER-v1.json').write_text(json.dumps(result, indent=2, ensure_ascii=False)+'\n')
print(json.dumps({'status':'DOCUMENT_CHECKS_MATCH','manifest_payloads':[m['matching_payloads'] for m in manifests],
                  'quotes':len(quotes),'receipt_checks':result['retained_receipt_checks'],
                  'seconds':result['seconds']}, indent=2))
