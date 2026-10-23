#!/usr/bin/env python3
"""Record measured license for the fixed tiny battery, before its full run."""
import json
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
OUT = ROOT / 'research/rmaf/results'
receipts = [OUT / f'algorithm-integration-fresh-review-{name}-v1.json'
            for name in ['pilot', 'size-pilot']]
data = [json.loads(p.read_text()) for p in receipts]
assert all(r['all_passed'] for r in data)
slowest = max(row['elapsed_seconds'] for r in data for row in r['rows'])
plan = {'pilot_receipts': [str(p.relative_to(ROOT)) for p in receipts],
        'pilot_controls': [r['completed'] for r in data],
        'slowest_measured_row_seconds': slowest,
        'fixed_full_control_count': 49,
        'projection_seconds': slowest * 49,
        'scaling_assumption': '49 fixed literal controls, maximum5 original leaves; slowest measured five-leaf operation row times49, not a future census/runtime bound',
        'progress_unit': 'completed exact literal controls and false expectations caught',
        'license': 'execute fixed49 only; stop and preserve any mismatch'}
dest = HERE / 'PILOT-PROJECTION.json'
assert not dest.exists()
dest.write_text(json.dumps(plan, indent=2) + '\n')
print(json.dumps(plan))
