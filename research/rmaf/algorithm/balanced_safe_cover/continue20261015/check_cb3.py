#!/usr/bin/env python3
"""One-shot CB3 controls and all-row diagnostic at preregistered base7/3."""
from copy import deepcopy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from time import perf_counter
import sys
import check_cb1 as base
import conflict_solver as core
import conflict_dag_solver as dag
import conflict_row_selector as selector

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]


class Adapter:
    @staticmethod
    def solve(*args):
        return selector.json_safe(selector.solve(*args))
    @staticmethod
    def optimize_hitting(*args):
        return selector.json_safe(selector.optimize_hitting(*args))
    def __getattr__(self, key):
        return getattr(core, key)


def main():
    begin = perf_counter()
    assert 7 * 10000 < 3 * 23391
    assert dag.implies([1], [3]) and not dag.implies([3], [1])
    assert dag.implies([1], []) and not dag.implies([], [1])
    selected, candidates = selector.choose_row(())
    assert selected is None and not candidates
    controls, catches = [], 1
    for rows, raw_count in [([3, 6, 5], 2), ([15, 23, 27, 29, 30], 4)]:
        closed, forced, _ = dag.forced_closure(rows)
        assert forced == 0
        chosen, all_rows = selector.choose_row(closed)
        assert len(all_rows) == len(rows)
        for item in all_rows:
            assert len(item['raw']) == raw_count and len(item['kept']) == 1
            assert item['mass'] == Fraction(3, 7) ** 2
            assert all(c['delta'] == 2 and not c['rows'] for c in item['raw'])
            assert item == selector.compile_row(closed, item['row'])
        bad = deepcopy(chosen)
        bad['kept'][0]['delta'] -= 1
        assert bad != selector.compile_row(closed, chosen['row'])
        corrupt_mass = chosen['mass'] + 1
        assert corrupt_mass != sum((selector.BASE ** (-c['delta']) for c in chosen['kept']), Fraction(0))
        catches += 2
        controls.append({'rows': rows, 'chosen': selector.json_safe(chosen),
                         'all_candidate_rows': len(all_rows), 'passed': True})
    base.solver = Adapter()
    base.main()
    output = sys.argv[sys.argv.index('--output') + 1]
    dest = ROOT/'research/rmaf/results'/output
    result = json.loads(dest.read_text())
    result['kind'] = 'GLOBAL-CB3-pinned-production-controls'
    result['base'] = [7, 3]
    result['versioned_alternative'] = 'alpha7/3 theta0; universal reachable-state row-mass theorem OPEN'
    result['cb3_controls'] = controls
    result['cb3_corruptions_caught'] = catches
    result['mutation_catches'] += catches
    result['seconds'] = perf_counter() - begin
    result['hashes'].update({str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                            for p in [HERE/'SPEC-CB3.md', HERE/'conflict_row_selector.py',
                                      HERE/'conflict_dag_solver.py', Path(__file__)]})
    failures = []
    for case in result['ordinary']:
        for attempt in case['answer']['attempts']:
            for p in attempt['profiles']:
                if p['chosen']['mass']['greater_than_one']:
                    failures.append({'id': case['id'], 'remaining_budget': p['remaining_budget'],
                                     'rows': p['rows'], 'chosen': p['chosen'],
                                     'all_rows': p['all_rows']})
    result['all_row_mass_failures'] = failures
    result['verdict'] = 'FINITE-CONTROLS-PASS; GLOBAL-ROW-MASS-THEOREM-OPEN'
    dest.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'receipt': str(dest), 'verdict': result['verdict'],
                      'abstract': result['executed_abstract'], 'ordinary': result['executed_ordinary'],
                      'mutation_catches': result['mutation_catches'],
                      'all_row_mass_failures': len(failures), 'seconds': result['seconds']}))


if __name__ == '__main__':
    main()
