"""One-shot complete-path construction/plant control, no project code import."""
import copy
import importlib.util
import json
from pathlib import Path

here = Path(__file__).parent
prereg = json.loads((here / 'FULL-PATH-CALIBRATION-PREREG-v1.json').read_text())
spec = importlib.util.spec_from_file_location('own_closed_check', here / 'closed-checks-v1.py')
own = importlib.util.module_from_spec(spec)
spec.loader.exec_module(own)
results = []
for key in ['positive', 'null']:
    entry = prereg[key]
    expected = {k: v for k, v in entry.items() if k not in ['T', 'S']}
    observed = own.optimize(entry['T'], entry['S'])
    compared = {k: observed[k] for k in expected}
    results.append({'name': key, 'expected': expected, 'observed': observed, 'matched': compared == expected})
bad = copy.deepcopy(results[0]['observed'])
bad['cuts'] = [[True]]
expected = results[0]['expected']
diag = 'FULL_PATH_EXACT_MISMATCH' if {k: bad[k] for k in expected} != expected else None
results.append({'name': 'corrupted_recovered_cut', 'diagnostic': diag, 'expected': prereg['corruption']['diagnostic'],
                'matched': diag == prereg['corruption']['diagnostic']})
assert len(results) == prereg['denominator']
matched = sum(r['matched'] for r in results)
out = here / 'full-path-calibration-observations-v1.json'
assert not out.exists()
out.write_text(json.dumps({'results': results, 'matched': matched, 'denominator': prereg['denominator']}, indent=2) + '\n')
for result in results:
    print(json.dumps({'name': result['name'], 'matched': result['matched'], 'diagnostic': result.get('diagnostic')}))
print('FULL_PATH_CALIBRATION matched=' + str(matched) + '/3')
raise SystemExit(0 if matched == 3 else 1)
