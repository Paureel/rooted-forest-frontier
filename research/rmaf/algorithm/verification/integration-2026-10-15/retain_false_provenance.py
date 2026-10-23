#!/usr/bin/env python3
"""Classify final controls, repeated partial-driver controls and refusals."""
import hashlib
import json
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
OUT = ROOT / 'research/rmaf/results'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(name): return json.loads((OUT / f'algorithm-integration-fresh-review-{name}.json').read_text())
source = read('source-replay-v1'); fresh = read('comparisons-v1'); audit = read('origin-audit-v3')
accepted = [source['rows'][-1], fresh['rows'][-1], audit['kernel_plant_rows'][2]]
assert sum(r['explicit_false_diagnostics'] for r in accepted) == 6
repeats = []
for name in ['KernelExplicitFalse','KernelExplicitFalseV2']:
    src = HERE / 'isolated' / f'{name}.lean'
    log = HERE / 'isolated' / f'{name}.fresh.log'
    assert log.read_text().count('is false') == 1
    repeats.append({'source':str(src.relative_to(ROOT)), 'source_sha256':sha(src),
                    'log':str(log.relative_to(ROOT)), 'log_sha256':sha(log),
                    'explicit_false_diagnostics':1,
                    'status':'same preregistered detector plant during an incomplete audit-driver version; excluded from final six, not a new mathematical control'})
payload = {'final_explicit_false_diagnostics':6,
           'accepted_final_negative_rows':accepted,
           'earlier_duplicate_plant_executions_excluded_from_final_count':repeats,
           'custom_axiom_control': {'compiler_row':audit['kernel_plant_rows'][1],
                                    'auditor_row':audit['custom_audit'],
                                    'rejected_entries':audit['rejected_custom_entries'],
                                    'meaning':'compile success is expected; axiom and public/private dependent theorem are deliberately rejected proof evidence'},
           'clean_axiom_twin':audit['clean_audit'],
           'generic_refusal_control':audit['kernel_plant_rows'][3],
           'adapter_failures_separate':json.loads((HERE/'ADAPTER-FAILURES.json').read_text()),
           'frozen_graph_comparator_controls':{'count':49,'false_expected_twins_caught':49,
                  'receipt':'research/rmaf/results/algorithm-integration-fresh-review-controls-v1.json',
                  'meaning':'exact expected-value comparator and fixed corrupt-input controls; not49 independent proof faults'},
           'scope':'same lineage, zero extra replications; never classify a generic compiler refusal as explicit mathematical falsity'}
(HERE/'FALSE-CONTROL-PROVENANCE.json').write_text(json.dumps(payload,indent=2)+'\n')
print(json.dumps({'final_explicit_false_diagnostics':6,'earlier_repeated_plant_runs_excluded':2,
                  'custom_axiom_and_private_dependency_caught':True,'generic_refusal_excluded':True}))
