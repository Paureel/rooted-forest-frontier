#!/usr/bin/env python3
"""Record a measured fixed-battery license, not an algorithm runtime claim."""
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];OUT=ROOT/'research/rmaf/results'
paths=[OUT/f'algorithm-core-work-fresh-review-{name}-v1.json' for name in ['pilot','size-pilot']]
data=[json.loads(p.read_text()) for p in paths]
assert all(r['all_passed'] for r in data)
slow=max(row['elapsed_seconds'] for r in data for row in r['rows'])
plan={'pilot_receipts':[str(p.relative_to(ROOT)) for p in paths],
      'slowest_measured_case_seconds':slow,'fixed_cases':29,
      'projection_seconds':29*slow,
      'assumption':'fixed tiny battery only: maximum4 original leaves, opaque join-left length16, fixed129-bit values; count scaling from slowest measured full4-leaf case including corruption validation',
      'measurement_scope':'Python reference evaluation plus report corruption/validation; excludes wrapper startup and is not Lean or source-machine runtime',
      'progress_unit':'completed literal ledger comparisons and corrupt reports caught',
      'license':'fixed29 controls/61 report plants only, stop on any failure; no census'}
dest=HERE/'PILOT-PROJECTION.json';assert not dest.exists()
dest.write_text(json.dumps(plan,indent=2)+'\n')
print(json.dumps(plan))
