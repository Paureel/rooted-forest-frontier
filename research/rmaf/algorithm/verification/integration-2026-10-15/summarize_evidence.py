#!/usr/bin/env python3
"""Reconcile final evidence without rerunning scientific checks."""
import hashlib
import json
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
OUT = ROOT / 'research/rmaf/results'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
ready_path = HERE / 'READY-ARTIFACTS.json'
assert sha(ready_path) == '1584dcd06fd529d413105fbfc0e377f5e0e4c25e982a66f44ba976f9a8346c2b'
ready = json.loads(ready_path.read_text())
assert len(ready['file_hashes']) == 26
for name, expected in ready['file_hashes'].items(): assert sha(ROOT / name) == expected, name
author = json.loads((HERE / 'CANDIDATE-PIN.json').read_text())
assert len(author['rows']) == 72
for r in author['rows']: assert sha(ROOT / r['path']) == r['expected_sha256'] == r['actual_sha256'], r['path']
for r in author['isolated_source_modules'].values(): assert sha(ROOT / r['copy']) == r['sha256']
def read(name): return json.loads((OUT / f'algorithm-integration-fresh-review-{name}.json').read_text())
controls = read('controls-v1'); sources = read('source-replay-v1'); audit = read('origin-audit-v3')
comparisons = read('comparisons-v1'); scope = read('scope-witnesses-v2')
assert all(r['all_passed'] for r in [controls,sources,audit,comparisons,scope])
rows = sources['rows'] + comparisons['rows'] + audit['kernel_plant_rows'] + [audit[k] for k in ['clean_audit','custom_audit','candidate_audit']]
rows += [scope['kernel_witness_row'],scope['own_evidence_audit']]
for r in rows:
    assert r['passed']
    assert sha(ROOT / r['source']) == r['source_sha256']
    assert sha(ROOT / r['log']) == r['log_sha256']
inventory = json.loads((HERE / 'AXIOM-INVENTORY.json').read_text())
assert sha(HERE / 'AXIOM-INVENTORY.json') == audit['inventory_sha256']
assert not inventory['violations']
assert len(inventory['entries']) == 1415
negative_count = sum(r.get('explicit_false_diagnostics', 0) for r in sources['rows'] + comparisons['rows'] + audit['kernel_plant_rows'])
assert negative_count == 6
failures = []
for name, mechanism in [('KernelCleanAudit','missing module header for import all'),
                         ('KernelCustomAudit','missing module header for import all'),
                         ('KernelCleanAuditV2','module header cannot import legacy non-module source'),
                         ('KernelCustomAuditV2','module header cannot import legacy non-module source'),
                         ('ScopeWitnesses','Decidable synthesis needs RootZeroOnly unfolded')]:
    source = HERE / 'isolated' / f'{name}.lean'
    log = HERE / 'isolated' / f'{name}.fresh.log'
    assert 'error:' in log.read_text() and 'is false' not in log.read_text()
    failures.append({'source': str(source.relative_to(ROOT)), 'source_sha256': sha(source),
                     'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log),
                     'classification': 'review adapter compiler refusal; not candidate counterexample or explicit false control',
                     'mechanism': mechanism})
(HERE / 'ADAPTER-FAILURES.json').write_text(json.dumps(failures, indent=2) + '\n')
summary = {'ready_artifacts_preserved': 26, 'author_immutable_files_match': 72,
           'frozen_controls': controls['completed'], 'clean_controls_passed': controls['clean_passed'],
           'false_expected_twins_caught': controls['false_expectations_caught'],
           'positive_frozen_source_modules': sources['positive_modules'],
           'candidate_originating_declarations': inventory['total_originating_declarations'],
           'private_originating_declarations': len(inventory['private_declarations']),
           'additional_to_author_explicit_inventory': len(inventory['additional_to_author_explicit_inventory']),
           'author_explicit_axiom_rows_matched': len(inventory['author449_comparison']),
           'compiled_finite_assertions': comparisons['assertions'],
           'frozen_controls_with_compiled_fields': comparisons['controls_with_compiled_fields'],
           'explicit_false_diagnostics_author': sum(r.get('explicit_false_diagnostics', 0) for r in sources['rows']),
           'explicit_false_diagnostics_fresh': sum(r.get('explicit_false_diagnostics', 0) for r in comparisons['rows']),
           'explicit_false_diagnostics_detector': sum(r.get('explicit_false_diagnostics', 0) for r in audit['kernel_plant_rows']),
           'explicit_false_diagnostics_total': negative_count,
           'post_contact_scope_witnesses': len(scope['witnesses']),
           'custom_axiom_and_private_dependency_caught': audit['custom_axiom_private_control_caught'],
           'axiom_violations': 0, 'additional_independent_replications': 0,
           'all_main_milestones': 'OPEN', 'all_retained_source_log_identities_match': True,
           'adapter_failures_retained': failures,
           'verified_compiler_rows': rows}
(HERE / 'EVIDENCE.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['adapter_failures_retained','verified_compiler_rows']}))
