#!/usr/bin/env python3
"""One-shot final source/log snapshot after scoped review and framing checks."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
OUT = ROOT / 'research/rmaf/results'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text())
ready = HERE / 'READY-ARTIFACTS.json'
assert sha(ready) == '1584dcd06fd529d413105fbfc0e377f5e0e4c25e982a66f44ba976f9a8346c2b'
for name, expected in read(ready)['file_hashes'].items(): assert sha(ROOT / name) == expected, name
pins = read(HERE / 'CANDIDATE-PIN.json')
assert pins['matched'] == 72 and sha(HERE / 'AUTHOR-MANIFEST-FROZEN.json') == pins['manifest_sha256']
assert sha(ROOT / 'research/rmaf/algorithm/universal233/INTEGRATION-MANIFEST-v1.json') == pins['manifest_sha256']
for r in pins['rows']: assert sha(ROOT / r['path']) == r['expected_sha256'] == r['actual_sha256'], r['path']
for r in pins['isolated_source_modules'].values(): assert sha(ROOT / r['copy']) == r['sha256']
evidence = read(HERE / 'EVIDENCE.json')
assert evidence['all_retained_source_log_identities_match'] and evidence['axiom_violations'] == 0
assert evidence['additional_independent_replications'] == 0
for r in evidence['verified_compiler_rows'] + evidence['adapter_failures_retained']:
    assert sha(ROOT / r['source']) == r['source_sha256']
    assert sha(ROOT / r['log']) == r['log_sha256']
inventory = read(HERE / 'AXIOM-INVENTORY.json')
assert len(inventory['entries']) == 1415 and len(inventory['private_declarations']) == 144
assert len(inventory['additional_to_author_explicit_inventory']) == 966
assert all(set(r['axioms']) <= {'propext','Classical.choice','Quot.sound'} and r['kind'] != 'axiom' for r in inventory['entries'])
assert all(r['found'] and r['axioms_match'] for r in inventory['author449_comparison'])
audit = read(OUT / 'algorithm-integration-fresh-review-origin-audit-v3.json')
assert audit['all_passed'] and audit['custom_axiom_private_control_caught']
assert sha(HERE / 'AXIOM-INVENTORY.json') == audit['inventory_sha256']
assert sha(HERE / 'audit_origins_v3.py') == audit['source_sha256']
kernel = read(HERE / 'KERNEL-CONTROL-PIN.json')
for r, p in zip(audit['kernel_plant_rows'], kernel['plants']):
    assert (ROOT / r['source']).read_text() == p['source']
mapping = read(HERE / 'COMPARISON-MAP.json')
for name, expected in mapping['sources_sha256'].items(): assert sha(ROOT / name) == expected
comparisons = read(OUT / 'algorithm-integration-fresh-review-comparisons-v1.json')
assert comparisons['all_passed'] and comparisons['assertions'] == 76 and comparisons['controls_with_compiled_fields'] == 30
assert sha(HERE / 'generate_comparisons.py') == comparisons['generator_sha256']
assert sha(HERE / 'COMPARISON-MAP.json') == comparisons['map_sha256']
source = read(OUT / 'algorithm-integration-fresh-review-source-replay-v1.json')
assert source['all_passed'] and source['positive_modules'] == 18
assert sha(HERE / 'replay_sources.py') == source['source_sha256']
scope = read(OUT / 'algorithm-integration-fresh-review-scope-witnesses-v2.json')
assert scope['all_passed'] and len(scope['witnesses']) == 6
assert not scope['own_evidence_axiom_violations']
assert sha(HERE / 'replay_scope_v2.py') == scope['source_sha256']
clean = read(OUT / 'algorithm-integration-fresh-review-transcription.json')
false = read(OUT / 'algorithm-integration-fresh-review-transcription-false.json')
assert clean['matches'] == clean['headlines_emitted'] == 18 and clean['findings_count'] == 0
assert false['matches'] == 0 and false['findings_count'] == 1
trace = read(HERE / 'CONSUMER-TRACE.json')
assert len(trace['claims']) == 23 and all(s == 'OPEN' for s in trace['all_main_milestones'].values())
assert not trace['source_core_or_full_solver_accepted']
for r in trace['claims']:
    assert r['source_locator'] and r['consumer_locator']
    if r['verdict'] == 'REFUTED-AT-WITNESS': assert r['witness']
    if r['verdict'] == 'OPEN-AT-NAMED-OBLIGATION': assert r['remaining_obligation'] and not r['exact_hypotheses']
review = (HERE / 'referee_sim_VERDICT.md').read_text()
assert sha(HERE / 'VERDICT.md') in review and sha(HERE / 'CONSUMER-TRACE.json') in review
files = sorted([p for p in HERE.rglob('*') if p.is_file() and p.name != 'ARTIFACTS.json'
                and '__pycache__' not in p.parts] + list(OUT.glob('algorithm-integration-fresh-review-*')))
manifest = {'created_utc': datetime.now(timezone.utc).isoformat(),
            'scope': 'CONFIRMED-SCOPED frozen local source integration only; zero extra independent replications',
            'report': str((HERE / 'VERDICT.md').relative_to(ROOT)),
            'consumer_trace': str((HERE / 'CONSUMER-TRACE.json').relative_to(ROOT)),
            'axiom_inventory': str((HERE / 'AXIOM-INVENTORY.json').relative_to(ROOT)),
            'author_manifest_sha256': pins['manifest_sha256'],
            'ready_manifest_sha256': sha(ready),
            'all_main_milestones': trace['all_main_milestones'],
            'open_obligations': ['OPEN-ORIGINAL-RESIDUAL-COMPONENTS','OPEN-FINITE-BUDGET-COVERAGE','OPEN-REALIZED-COST-MASS-WORK','complete algorithm/universal correctness/smaller base'],
            'all_retained_frozen_source_and_log_identities_match': True,
            'file_hashes': {str(p.relative_to(ROOT)): sha(p) for p in files},
            'manifest_excludes_itself_and_python_caches': True}
dest = HERE / 'ARTIFACTS.json'
assert not dest.exists()
dest.write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'files_hashed': len(files), 'manifest_sha256': sha(dest),
                  'scope': manifest['scope'], 'all_main_milestones': 'OPEN'}))
