#!/usr/bin/env python3
"""Known clean/false scalar detector controls over retained actual observations."""
import copy
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
source = json.loads((HERE / 'PAID-SCHEDULER-EXPECTATIONS-v1.json').read_text())
spec = json.loads((HERE / 'PAID-SCHEDULER-CHECK-EXPECTATIONS-v2.json').read_text())
rows = json.loads((HERE / 'paid-scheduler-full-v1.json').read_text())
expected = {r['id']: r for r in source['cases']}


def check(row):
    e = expected[row['id']]
    for field in ('calls', 'answers', 'recursiveWork'):
        assert row[field] == e[field], (row['id'], field)
    assert [p[1] for p in row['queries']] == e['calls']


start = time.perf_counter()
pilot = next(r for r in rows if r['id'] == 'second_failure')
check(pilot)
false_pilot = copy.deepcopy(pilot)
false_pilot['recursiveWork'] = 12
try:
    check(false_pilot)
except AssertionError:
    pass
else:
    raise AssertionError('failed-call billing plant survived')
pilot_seconds = time.perf_counter() - start
start = time.perf_counter()
assert len(rows) == spec['clean_rows'] and len({r['id'] for r in rows}) == len(rows)
for row in rows:
    check(row)
twins = []
for mutation in spec['false_twins']:
    bad = copy.deepcopy(next(r for r in rows if r['id'] == mutation['id']))
    bad[mutation['field']] = mutation['false_value']
    try:
        check(bad)
    except AssertionError:
        twins.append({**mutation, 'caught': True})
    else:
        raise AssertionError('scalar false twin survived: ' + str(mutation))
result = {'passed': True, 'context': spec['context'], 'clean_rows': len(rows),
          'pilot_seconds': pilot_seconds, 'full_seconds': time.perf_counter() - start,
          'false_twins': twins, 'new_Lean_execution': False}
(HERE / 'paid-scheduler-detector-controls-v2.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
