#!/usr/bin/env python3
"""One-shot CB2 controls extending the unchanged CB1 pinned harness."""
from copy import deepcopy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from time import perf_counter
import sys
import conflict_dag_solver as dag
import conflict_solver as core
import check_cb1 as base

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]


class SolverAdapter:
    optimize_hitting = staticmethod(dag.optimize_hitting)
    solve = staticmethod(dag.solve)
    def __getattr__(self, key):
        return getattr(core, key)


def main():
    begin = perf_counter()
    controls = []
    assert dag.implies([1], [3]) and not dag.implies([3], [1])
    assert dag.implies([1], []) and not dag.implies([], [1])
    assert dag.dominates({'delta': 1, 'rows': (3,)}, {'delta': 2, 'rows': (1,)})
    assert not dag.dominates({'delta': 2, 'rows': (1,)}, {'delta': 1, 'rows': (3,)})
    controls.append({'id': 'monotone-cnf-direction-and-prefix-cost', 'passed': True,
                     'reversed-false-control-rejected': not dag.implies([3], [1])})
    corruptions = 1
    for rows, count in [([3, 6, 5], 2), ([15, 23, 27, 29, 30], 4)]:
        closed, forced, _ = dag.forced_closure(rows)
        assert forced == 0
        raw, kept = dag.compile_children(closed)
        assert len(raw) == count and len(kept) == 1
        assert all(t['delta'] == 2 and not t['rows'] for t in raw)
        assert dag.verify_compilation(closed, raw, kept)
        bad = deepcopy(raw)
        bad[0]['delta'] -= 1
        assert not dag.verify_compilation(closed, bad, kept)
        corruptions += 1
        controls.append({'id': 'terminal-prefix-dedup', 'rows': rows, 'raw': raw, 'kept': kept})
    answer = dag.solve(['a', 'b'], ['a', 'b'], 0)
    assert answer['cost'] == 0
    answer = dag.solve([['a', 'b'], ['c', 'd']], [['a', 'c'], ['b', 'd']], 2)
    bad = deepcopy(answer['certificate'])
    bad['original_source_edge_indices'].append(bad['original_source_edge_indices'][0])
    assert core.verify_certificate([['a', 'b'], ['c', 'd']], [['a', 'c'], ['b', 'd']], 2,
                                   answer['certificate'])
    assert not core.verify_certificate([['a', 'b'], ['c', 'd']], [['a', 'c'], ['b', 'd']], 3, bad)
    corruptions += 1
    base.solver = SolverAdapter()
    base.main()
    args = sys.argv
    output = args[args.index('--output') + 1]
    dest = ROOT/'research/rmaf/results'/output
    result = json.loads(dest.read_text())
    result['kind'] = 'GLOBAL-CB2-pinned-production-controls'
    result['cb2_structural_controls'] = controls
    result['cb2_structural_corruptions_caught'] = corruptions
    result['mutation_catches'] += corruptions
    result['seconds'] += perf_counter() - begin
    result['hashes'].update({str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                            for p in [HERE/'SPEC-CB2.md', HERE/'conflict_dag_solver.py', Path(__file__)]})
    mass_failures = []
    for case in result['ordinary']:
        for attempt in case['answer']['attempts']:
            for profile in attempt['profiles']:
                mass = sum((Fraction(23391,10000) ** (-c['delta']) for c in profile['kept']), Fraction(0))
                if mass > 1:
                    mass_failures.append({'id': case['id'], 'rows': profile['rows'],
                                          'remaining_budget': profile['remaining_budget'],
                                          'deltas': [c['delta'] for c in profile['kept']],
                                          'mass': [mass.numerator, mass.denominator]})
    result['uniform_benchmark_mass_failures'] = mass_failures
    result['verdict'] = 'FINITE-CONTROLS-PASS; COMPILED-DAG-BOUND-OPEN'
    dest.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'receipt': str(dest), 'verdict': result['verdict'],
                      'abstract': result['executed_abstract'], 'ordinary': result['executed_ordinary'],
                      'mutation_catches': result['mutation_catches'],
                      'uniform_benchmark_mass_failures': len(mass_failures),
                      'seconds': result['seconds']}))


if __name__ == '__main__':
    main()
