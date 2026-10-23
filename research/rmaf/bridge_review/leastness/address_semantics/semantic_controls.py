"""One-shot exact semantic controls; standalone stack traversal, no Lean imports.
The toolkit index has no binary-tree occurrence semantics instrument. This local
harness freezes problem-specific hand-written fixtures, not a reusable engine.
"""
import copy
import hashlib
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
start = time.monotonic()
controls = json.loads((HERE / 'controls.json').read_text())

def direct(tree, selected):
    pending = [(tree, '')]
    vertices, leaves = [], []
    while pending:
        subtree, address = pending.pop()
        vertices.append(address)
        if isinstance(subtree, int):
            leaves.append([address, subtree])
        else:
            pending.append((subtree[1], address + '1'))
            pending.append((subtree[0], address + '0'))
    return {'vertices': vertices, 'occurrences': leaves,
            'terminals': [a for a, x in leaves if x in selected]}

def check(expected, candidate):
    return all(candidate[key] == expected[key]
               for key in ('vertices', 'occurrences', 'terminals'))

rows = []
for f in controls['fixtures']:
    actual = direct(f['tree'], f['selection'])
    assert check(f, actual), f['id']
    rows.append({'id': f['id'], 'status': 'pass'})
assert len(rows) == 6
fixture = next(f for f in controls['fixtures'] if f['id'] == 'duplicates')
truth = direct(fixture['tree'], fixture['selection'])
mutants = []
for name, key, replacement in [
    ('invalid_ambient', 'vertices', truth['vertices'] + ['000']),
    ('missing_occurrence', 'terminals', ['0']),
    ('duplicate_selection_multiplies_occurrences', 'terminals', ['0', '10', '0', '10']),
    ('internal_root_is_terminal', 'terminals', ['', '0', '10']),
    ('wrong_leaf_label', 'occurrences', [['0', 5], ['10', 6], ['11', 8]])]:
    candidate = copy.deepcopy(truth)
    candidate[key] = replacement
    assert not check(fixture, candidate), name
    assert check(fixture, truth), name + '_clean_twin'
    mutants.append({'id': name, 'status': 'caught', 'clean_twin': 'pass'})
receipt = {'fixtures': rows, 'corruptions': mutants,
           'elapsed_seconds': time.monotonic() - start,
           'provenance': 'Same author and mathematical address convention as proof; no shared candidate source, no extraction code. Development controls, not an independent nonauthor certification.',
           'controls_sha256': hashlib.sha256((HERE / 'controls.json').read_bytes()).hexdigest()}
(HERE / 'semantic-controls.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('PASS: 6/6 exact semantic fixtures; 5/5 corruptions caught with clean twins.')
