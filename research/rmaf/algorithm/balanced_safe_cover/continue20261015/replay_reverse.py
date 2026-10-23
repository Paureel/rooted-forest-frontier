#!/usr/bin/env python3
"""One-shot nonauthor finite replay of the completed child's CB1 family.

Parent CB1 code predates the family and shares no child implementation. These
finite checks do not formalize the universal quotient invariant.
"""
from datetime import datetime, timezone
import hashlib
import itertools
import json
from pathlib import Path
from time import perf_counter
import conflict_solver as solver

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]


def pair(b):
    labels = tuple('x' + str(i) for i in range(1, 2*b+2))
    s = labels[-1]
    for label in reversed(labels[:-1]):
        s = (label, s)
    t = labels[0]
    for label in labels[1:]:
        t = (label, t)
    return labels, s, t


def main():
    begin = perf_counter()
    rows, catches = [], 0
    for b in range(1, 7):
        started = perf_counter()
        labels, s, t = pair(b)
        S, T = solver.validate_input(s, t, b)
        assert all(S.restrict(q) != T.restrict(q) for q in itertools.combinations(labels, 3))
        H = tuple(solver.conflicts(S,T))
        factors = solver.incidence_factors(H)
        assert len(factors) == 1
        stats = {'initial_budget': b-1, 'nodes': 0, 'max_depth': 0,
                 'max_branch_rank': 0, 'branch_rank_histogram': {}}
        failed = solver.bounded_search(factors[0], b-1, stats)
        assert failed is None and stats['nodes'] == 2**b - 1
        try:
            assert stats['nodes'] == 2**b
        except AssertionError:
            catches += 1
        else:
            raise AssertionError('off-by-one false node control survived')
        whole = solver.solve(s, t, b)
        assert whole['status'] == 'SOLVED' and whole['cost'] == b
        assert whole['nodes'] == 2**(b+1) - 1
        receipt_edges = S.edge_receipt((1 << len(S.edges)) - 1)
        expected_splits = [set(labels[i:]) for i in range(2, 2*b, 2)]
        expected_splits.append({labels[-1]})
        witness_mask = 0
        for split in expected_splits:
            candidates = [e['edge'] for e in receipt_edges if set(e['child_labels']) == split]
            assert len(candidates) == 1
            witness_mask |= 1 << candidates[0]
        witness = solver.certificate_for(S, T, witness_mask)
        assert witness['total_cost'] == b
        assert solver.verify_certificate(s, t, b, witness)
        rows.append({'b': b, 'N': len(labels), 'source': s, 'target': t,
                     'factor_count': len(factors), 'failed_trial_budget': b-1,
                     'failed_trial_nodes': stats['nodes'], 'expected_failed_trial_nodes': 2**b-1,
                     'all_trials_nodes': whole['nodes'], 'expected_all_trials_nodes': 2**(b+1)-1,
                     'original_source_witness': witness, 'seconds': perf_counter()-started})
    result = {'kind': 'GLOBAL-CB1-nonauthor-reverse-family-finite-replay',
              'date': datetime.now(timezone.utc).isoformat(), 'rows': rows,
              'expected_family_cases': 6, 'executed_family_cases': len(rows),
              'node_comparator_corruptions_caught': catches,
              'lineage': 'parent production CB1 code was frozen before child proposed the family; no child code reused; deepest shared dependency is mathematical model only',
              'scope': 'independent implementation finite replay and direct source certificate check; universal source-family invariant remains handwritten, not Lean-closed',
              'proof_source': 'research/rmaf/algorithm/balanced_safe_cover/continue20261015/adversary/REVERSE-CATERPILLAR-LOWER-BOUND.md',
              'hashes': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in [HERE/'conflict_solver.py', Path(__file__),
                                   HERE/'adversary/REVERSE-CATERPILLAR-LOWER-BOUND.md']},
              'seconds': perf_counter()-begin}
    dest = ROOT/'research/rmaf/results/algorithm-balanced-cover-continue-reverse-nonauthor-replay.json'
    dest.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'receipt': str(dest), 'family_cases': len(rows),
                      'failed_trial_counts': [r['failed_trial_nodes'] for r in rows],
                      'corruptions_caught': catches, 'seconds': result['seconds']}))


if __name__ == '__main__':
    main()
