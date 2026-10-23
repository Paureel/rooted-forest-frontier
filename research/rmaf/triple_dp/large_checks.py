"""Problem-specific witness-only scale checks and a baseline child example.
The large-case costs are DP output, not independently certified optima.
"""
import hashlib
import json
import pathlib
import random
import time
import cut_oracle
import solver

HERE = pathlib.Path(__file__).resolve().parent


def balanced(labels):
    if len(labels) == 1:
        return labels[0]
    mid = len(labels) // 2
    return balanced(labels[:mid]), balanced(labels[mid:])


def run():
    controls = json.loads((HERE / 'controls.json').read_text())
    for case in controls['positive']:
        assert cut_oracle.check_witness(case, solver.solve(case)['partition'])
    bad = next(c for c in controls['positive'] if c['id'] == 'good-overlap')
    try:
        cut_oracle.check_witness(bad, [['a', 'b'], ['c', 'd']])
    except ValueError as e:
        assert 'overlapping' in str(e)
    else:
        raise AssertionError('corrupted witness not caught')
    rows = []
    for n in [60, 600]:
        labels = [f'x{i:04d}' for i in range(n)]
        shuffled = labels.copy()
        random.Random(20261014).shuffle(shuffled)
        case = {'target': balanced(shuffled),
                'source': [((labels[i], labels[i+1]), labels[i+2]) for i in range(0, n, 3)]}
        start = time.perf_counter()
        answer = solver.solve(case)
        elapsed = time.perf_counter() - start
        start = time.perf_counter()
        cut_oracle.check_witness(case, answer['partition'])
        checked = time.perf_counter() - start
        rows.append(dict(n=n, m=n//3, seed=20261014, answer=answer,
                         solver_seconds=elapsed, witness_seconds=checked,
                         status='witness checked; optimum NOT independently checked'))
    out = dict(controls=dict(positive=5, corruption_caught=1), rows=rows,
               source_hashes={f: hashlib.sha256((HERE/f).read_bytes()).hexdigest()
                              for f in ['solver.py', 'cut_oracle.py', 'large_checks.py']})
    (HERE.parent/'results/triple-dp-large-witness-replay.json').write_text(json.dumps(out, indent=2)+'\n')

    # Post-hoc illustrative branch, not part of the frozen acceptance battery.
    # Rule 4, branch 2, of the locally read baseline text: cut off a.
    target = (('a', 'b'), ('c', 'd'))
    original = {'target': target, 'source': [(('a', 'c'), ('b', 'd'))]}
    child = {'target': target, 'source': ['a', ('c', ('b', 'd'))]}
    answer = solver.solve(child)
    assert answer['components'] == cut_oracle.solve(child) == 3
    assert answer['additional_cuts'] == 1
    assert cut_oracle.solve(original) == 3
    assert cut_oracle.check_witness(child, answer['partition'])
    source_signature = tuple(sorted(next(f for f in cut_oracle.cut_forests(cut_oracle.freeze(t))
                                         if len(f) == 1)[0] for t in child['source']))
    assert source_signature in cut_oracle.cut_forests(cut_oracle.freeze(original['source'][0]))
    record = dict(original=original, child=child, result=answer, already_paid_cuts=1,
                  original_optimum_components=3, total_cuts=2,
                  source='sources/baseline/split-or-decompose-v2.txt',
                  locator='PDF pp.17–18, Branching rule 4, branch 2; Figure 16 p.24',
                  scope='A single legal reachable child. No safe cover, universal branch improvement, or novelty claim.')
    (HERE.parent/'results/triple-dp-baseline-child.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps(dict(witness_cases=len(rows), baseline_child_checked=True,
                          large_optimality='not independently checked')))


if __name__ == '__main__':
    run()
