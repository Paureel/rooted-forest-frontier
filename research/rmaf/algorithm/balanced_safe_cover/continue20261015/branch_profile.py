#!/usr/bin/env python3
"""One-shot GLOBAL-CB1 exact compressed-transition diagnostic; no oracle."""
from copy import deepcopy
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from time import perf_counter
import conflict_solver as solver

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]


def forced_closure(rows):
    selected = 0
    steps = []
    while rows:
        rows = solver.quotient_rows(rows)
        row = min(rows, key=lambda h: (h.bit_count(), h))
        if row.bit_count() != 1:
            break
        edge = next(solver.bits(row))
        steps.append({'edge': edge, 'before': list(rows)})
        selected |= row
        rows = tuple(h for h in rows if not h & row)
    return rows, selected, steps


def profile(rows):
    rows, selected, steps = forced_closure(rows)
    out = {'forced_before_branch': list(solver.bits(selected)), 'initial_forcing_steps': steps,
           'branch_rows': list(rows), 'branch_row': None, 'transitions': []}
    if not rows:
        return out
    row = min(rows, key=lambda h: (h.bit_count(), h))
    out['branch_row'] = row
    for e in solver.bits(row):
        bit = 1 << e
        residual = tuple(h for h in rows if not h & bit)
        after, forced, forced_steps = forced_closure(residual)
        cuts = bit | forced
        out['transitions'].append({'branch_edge': e, 'forced_steps': forced_steps,
                                   'cut_edges': list(solver.bits(cuts)),
                                   'delta': cuts.bit_count(), 'after': list(after)})
    return out


def verify_profile(rows, supplied):
    # Reconstruct from pinned literal transition definitions; no optimizer.
    return supplied == profile(rows)


def mass(transitions, base):
    return sum((base ** (-t['delta']) for t in transitions), Fraction(0))


def exact(frac):
    return {'numerator': frac.numerator, 'denominator': frac.denominator,
            'greater_than_one': frac > 1}


def main():
    started = perf_counter()
    controls = [([], []), ([3, 6, 5], [2, 2]), ([15, 23, 27, 29, 30], [2, 2, 2, 2])]
    control_rows = []
    caught = 0
    for rows, expected in controls:
        p = profile(rows)
        assert [t['delta'] for t in p['transitions']] == expected
        assert verify_profile(rows, p)
        if p['transitions']:
            bad = deepcopy(p)
            bad['transitions'][0]['delta'] -= 1
            assert not verify_profile(rows, bad)
            caught += 1
        control_rows.append({'rows': rows, 'expected_deltas': expected, 'profile': p})
    fixtures = json.loads((HERE/'CONTROLS-CB1.json').read_text())['ordinary']
    cases = []
    benchmark = Fraction(23391, 10000)
    for f in fixtures:
        S, T = solver.validate_input(f['source'], f['target'], f['optimum'])
        H = tuple(solver.conflicts(S, T))
        seen = set()
        profiles = []
        def visit(rows, remaining):
            key = (tuple(rows), remaining)
            if key in seen:
                return
            seen.add(key)
            p = profile(rows)
            assert verify_profile(rows, p)
            p['remaining_budget'] = remaining
            p['benchmark_mass'] = exact(mass(p['transitions'], benchmark))
            p['base_two_mass'] = exact(mass(p['transitions'], Fraction(2)))
            profiles.append(p)
            left = remaining - len(p['forced_before_branch'])
            for t in p['transitions']:
                if t['delta'] <= left:
                    visit(tuple(t['after']), left - t['delta'])
        for factor in solver.incidence_factors(H):
            visit(factor, f['optimum'])
        failures = [p for p in profiles if p['benchmark_mass']['greater_than_one']]
        cases.append({'id': f['id'], 'source': f['source'], 'target': f['target'],
                      'budget': f['optimum'], 'original_edges': S.edge_receipt((1 << len(S.edges)) - 1),
                      'profile_count': len(profiles), 'benchmark_mass_failures': len(failures),
                      'profiles': profiles})
    report = {'kind': 'GLOBAL-CB1-compressed-branch-profiles',
              'verdict': 'FINITE-DIAGNOSTIC; NO-UNIVERSAL-RECURRENCE',
              'date': datetime.now(timezone.utc).isoformat(), 'controls': control_rows,
              'corruptions_caught': caught, 'ordinary_expected': len(fixtures),
              'ordinary_executed': len(cases), 'cases': cases,
              'seconds': perf_counter() - started,
              'lineage': 'same author and original GLOBAL-C tree/conflict primitives; development evidence only',
              'hashes': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in [HERE/'PROFILE-PIN.md', HERE/'CONTROLS-CB1.json',
                                   HERE/'conflict_solver.py', Path(__file__)]}}
    dest = ROOT/'research/rmaf/results/algorithm-balanced-cover-continue-cb1-profiles.json'
    dest.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'receipt': str(dest), 'controls': len(controls),
                      'corruptions_caught': caught, 'ordinary': len(cases),
                      'profiles': sum(c['profile_count'] for c in cases),
                      'benchmark_mass_failures': sum(c['benchmark_mass_failures'] for c in cases),
                      'seconds': report['seconds']}))


if __name__ == '__main__':
    main()
