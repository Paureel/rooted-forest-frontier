"""One-shot bounded geometry guard attack; not an arbitrary-N proof."""
import importlib.util
import itertools
import json
from pathlib import Path

here = Path(__file__).parent
prereg = json.loads((here / 'GEOMETRY-PREREG-v1.json').read_text())
spec = importlib.util.spec_from_file_location('own_closed_check', here / 'closed-checks-v1.py')
own = importlib.util.module_from_spec(spec)
spec.loader.exec_module(own)


def incident(t, x):
    hull = own.minimal(x, t)
    return [p for p in own.vertices(t) if p and ((p in hull) != (p[:-1] in hull))]


def split(t, x, allow_y=True):
    y = [a for a in own.leaves(t) if a not in x]
    return any(sorted(own.leaves(own.subtree(t, p))) == sorted(x) or
               (allow_y and sorted(own.leaves(own.subtree(t, p))) == sorted(y))
               for p in own.vertices(t) if p)


controls = []
for c in prereg['controls']:
    actual = {'incident': incident(c['T'], c['X']), 'split': split(c['T'], c['X'])}
    expected = {'incident': c['incident'], 'split': c['split']}
    controls.append({'name': c['name'], 'actual': actual, 'expected': expected, 'matched': actual == expected})
c = prereg['controls'][1]
diagnostic = 'MISSING_COMPLEMENT_SIDE' if len(incident(c['T'], c['X'])) == 1 and not split(c['T'], c['X'], False) else None
controls.append({'name': 'delete_Y_alternative', 'actual': diagnostic, 'expected': prereg['corruption']['expected_diagnostic'],
                 'matched': diagnostic == prereg['corruption']['expected_diagnostic']})
controls_ok = len(controls) == prereg['control_denominator'] and all(c['matched'] for c in controls)


def shapes(n):
    if n == 1:
        return [None]
    return [(a, b) for i in range(1, n) for a in shapes(i) for b in shapes(n-i)]


def fill(shape, labels):
    return next(labels) if shape is None else [fill(shape[0], labels), fill(shape[1], labels)]


observations, witnesses = [], []
if controls_ok:
    for expected in prereg['enumeration']:
        n = expected['N']
        actual = {'N': n, 'trees': 0, 'partition_cases': 0, 'singleton_incident': 0, 'original_split': 0, 'disagreements': 0}
        for shape in shapes(n):
            for perm in itertools.permutations(range(n)):
                t = fill(shape, iter(perm))
                actual['trees'] += 1
                for bits in range(1, 2**n - 1):
                    x = [i for i in range(n) if bits & (1 << i)]
                    boundary = incident(t, x)
                    one, side = len(boundary) == 1, split(t, x)
                    actual['partition_cases'] += 1
                    actual['singleton_incident'] += one
                    actual['original_split'] += side
                    if one != side:
                        actual['disagreements'] += 1
                        witnesses.append({'T': t, 'X': x, 'incident': boundary, 'original_split': side})
        observations.append({'actual': actual, 'expected': expected, 'matched': actual == expected})
accepted = controls_ok and len(observations) == 3 and all(o['matched'] for o in observations)
out = here / 'geometry-observations-v1.json'
assert not out.exists()
out.write_text(json.dumps({'controls': controls, 'control_denominator': 4, 'observations': observations,
                           'witnesses': witnesses, 'expectations_matched': accepted}, indent=2) + '\n')
for c in controls:
    print(json.dumps(c))
for row in observations:
    print(json.dumps(row))
print('GEOMETRY_EXPECTATIONS matched=' + str(accepted))
raise SystemExit(0 if accepted else 1)
