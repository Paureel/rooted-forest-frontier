#!/usr/bin/env python3
"""One-shot pinned controls for the new GLOBAL-CB1 production proposal.

The retained partition oracle is used only to score finite supplied fixtures;
it shares GLOBAL-C tree primitives and cannot independently certify the solver.
"""
import argparse
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from time import perf_counter
import conflict_solver as solver
import exact_conflicts as model

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
FIXTURES = HERE / 'CONTROLS-CB1.json'


def insist(value, expected):
    if value != expected:
        raise AssertionError({'actual': value, 'expected': expected})


def compare_mutation(value, expected):
    try:
        insist(value, expected)
    except AssertionError:
        return True
    raise AssertionError('deliberate comparator corruption survived')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--ordinary-limit', type=int, default=9)
    ap.add_argument('--output', required=True)
    args = ap.parse_args()
    started = perf_counter()
    fixtures = json.loads(FIXTURES.read_text())
    assert 0 <= args.ordinary_limit <= len(fixtures['ordinary'])
    abstract, ordinary, mutations = [], [], []
    for f in fixtures['abstract']:
        begin = perf_counter()
        answer = solver.optimize_hitting(f['rows'], f['optimum'])
        insist(answer['status'], 'SOLVED')
        insist(answer['cost'], f['optimum'])
        insist(answer['factor_count'], f['factors'])
        if f['optimum']:
            failure = solver.optimize_hitting(f['rows'], f['optimum'] - 1)
            insist(failure['status'], 'BUDGET_FAILURE')
            assert failure['spent'] + failure['failure_factor_lower_bound'] > f['optimum'] - 1
        assert compare_mutation(answer['cost'], f['optimum'] + 1)
        mutations.append({'id': f['id'], 'kind': 'abstract-optimum-comparator', 'caught': True})
        abstract.append({'id': f['id'], 'answer': answer, 'seconds': perf_counter() - begin})
    # False exponent deliberately presented to the exact comparator.
    assert compare_mutation(2 * 2, 3)
    assert 2 * 10000 < 23391
    mutations.append({'id': 'false-alpha-two', 'kind': 'three-halves-at-least-two', 'caught': True})
    for f in fixtures['ordinary'][:args.ordinary_limit]:
        begin = perf_counter()
        S, T = solver.validate_input(f['source'], f['target'], f['optimum'])
        # Production-side development oracle; already contacted values are not held out.
        oracle_cost = model.oracle(S, T)[0]
        insist(oracle_cost, f['optimum'])
        answer = solver.solve(f['source'], f['target'], f['optimum'])
        insist(answer['status'], 'SOLVED')
        insist(answer['cost'], f['optimum'])
        cert = answer['certificate']
        assert solver.verify_certificate(f['source'], f['target'], f['optimum'], cert)
        # At a larger supplied budget, one ORIGINAL optimum must still be returned.
        looser = solver.solve(f['source'], f['target'], f['optimum'] + 2)
        insist(looser['cost'], f['optimum'])
        if f['optimum']:
            failure = solver.solve(f['source'], f['target'], f['optimum'] - 1)
            insist(failure['status'], 'BUDGET_FAILURE')
        bad = deepcopy(cert)
        bad['precut_cost'] += 1
        assert not solver.verify_certificate(f['source'], f['target'], f['optimum'] + 2, bad)
        mutations.append({'id': f['id'], 'kind': 'precut-accounting', 'caught': True})
        if cert['components']:
            for field, entry in [('original_labels', '__corrupt__'), ('target_support', 999999)]:
                bad = deepcopy(cert)
                bad['components'][0][field].append(entry)
                assert not solver.verify_certificate(f['source'], f['target'], f['optimum'] + 2, bad)
                mutations.append({'id': f['id'], 'kind': field, 'caught': True})
        # Ensure no hidden exact optimizer is reached in the production entry point.
        banned = ['oracle', 'partitions', 'packing', 'exact_row']
        saved = {name: getattr(model, name) for name in banned}
        def forbidden(*unused_args, **unused_kwargs):
            raise AssertionError('production called a test oracle')
        try:
            for name in banned:
                setattr(model, name, forbidden)
            direct = solver.solve(f['source'], f['target'], f['optimum'] + 2)
            insist(direct['cost'], f['optimum'])
        finally:
            for name, value in saved.items():
                setattr(model, name, value)
        ordinary.append({'id': f['id'], 'expected_original_optimum': f['optimum'],
                         'partition_oracle_optimum': oracle_cost, 'answer': answer,
                         'looser_budget_original_optimum': looser['cost'],
                         'test_oracles_blocked_in_production': True,
                         'seconds': perf_counter() - begin})
    # Null and malformed entry controls exercise validation directly.
    invalid = [(['a', 'a'], ['a', 'b'], 1), (['a', 'b', 'c'], ['a', 'b'], 1),
               (['a', 'b'], ['a', 'c'], 1), ('a', 'a', -1), ('a', 'a', True)]
    for s, t, b in invalid:
        try:
            solver.solve(s, t, b)
        except ValueError:
            mutations.append({'kind': 'malformed-input', 'source': s, 'target': t,
                              'budget': b, 'caught': True})
        else:
            raise AssertionError('malformed input accepted')
    expected_abstract, expected_ordinary = len(fixtures['abstract']), args.ordinary_limit
    assert len(abstract) == expected_abstract and len(ordinary) == expected_ordinary
    report = {'kind': 'GLOBAL-CB1-pinned-production-controls',
              'verdict': 'FINITE-CONTROLS-PASS; UNIVERSAL-BOUND-OPEN',
              'date': datetime.now(timezone.utc).isoformat(),
              'expected_abstract': expected_abstract, 'executed_abstract': len(abstract),
              'expected_ordinary': expected_ordinary, 'executed_ordinary': len(ordinary),
              'abstract': abstract, 'ordinary': ordinary,
              'mutations': mutations, 'mutation_catches': len(mutations),
              'seconds': perf_counter() - started,
              'lineage': 'GLOBAL-C Tree/conflicts/partition primitives shared; same continuation author; finite production scoring only',
              'hashes': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in [FIXTURES, HERE/'SPEC-CB1.md', HERE/'conflict_solver.py',
                                   Path(__file__), solver.CONFLICT_DIR/'exact_conflicts.py']}}
    dest = ROOT / 'research/rmaf/results' / args.output
    dest.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'verdict': report['verdict'], 'abstract': len(abstract),
                      'ordinary': len(ordinary), 'mutation_catches': len(mutations),
                      'seconds': report['seconds'], 'receipt': str(dest)}))


if __name__ == '__main__':
    main()
