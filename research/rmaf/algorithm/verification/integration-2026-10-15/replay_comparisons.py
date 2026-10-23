#!/usr/bin/env python3
"""Compile fresh source comparisons and their explicit-false frozen twins."""
import hashlib
import json
from pathlib import Path
from replay_sources import compile_one
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
OUT = ROOT / 'research/rmaf/results'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
mapping = json.loads((HERE / 'COMPARISON-MAP.json').read_text())
rows = [compile_one('FreshComparisons')]
if rows[0]['passed']:
    negative = compile_one('FreshComparisonsFalse', expected='nonzero')
    output = (ROOT / negative['log']).read_text()
    negative['explicit_false_diagnostics'] = output.count('is false')
    negative['passed'] &= negative['explicit_false_diagnostics'] == 2 and output.count('Tactic `decide` proved') == 2
    rows.append(negative)
receipt = {'scope': 'finite actual executable comparisons from pre-candidate literals; no whole-algorithm acceptance',
           'all_passed': len(rows) == 2 and all(r['passed'] for r in rows),
           'assertions': mapping['assertions'], 'controls_with_compiled_fields': mapping['controls_with_compiled_fields'],
           'rows': rows, 'map_sha256': sha(HERE / 'COMPARISON-MAP.json'),
           'generator_sha256': sha(HERE / 'generate_comparisons.py'), 'driver_sha256': sha(Path(__file__))}
dest = OUT / 'algorithm-integration-fresh-review-comparisons-v1.json'
assert not dest.exists()
dest.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({k: receipt[k] for k in ['all_passed', 'assertions', 'controls_with_compiled_fields']}))
raise SystemExit(0 if receipt['all_passed'] else 1)
