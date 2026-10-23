#!/usr/bin/env python3
"""One-shot GLOBAL-CB3 all-row structural compiler; universal mass is open."""
from fractions import Fraction
import conflict_solver as core
import conflict_dag_solver as dag

BASE = Fraction(7, 3)


def compile_row(rows, row):
    if row not in rows:
        raise ValueError('branch row must be a literal remaining conflict')
    raw = []
    for e in core.bits(row):
        bit = 1 << e
        residual, forced, steps = dag.forced_closure(tuple(h for h in rows if not h & bit))
        cuts = bit | forced
        raw.append({'branch_edge': e, 'rows': residual, 'cut_mask': cuts,
                    'delta': cuts.bit_count(), 'forcing_steps': steps})
    kept = []
    for candidate in sorted(raw, key=lambda c: (c['delta'], c['cut_mask'])):
        if any(dag.dominates(other, candidate) for other in kept):
            continue
        kept = [other for other in kept if not dag.dominates(candidate, other)]
        kept.append(candidate)
    if not kept or not all(any(dag.dominates(k, child) for k in kept) for child in raw):
        raise AssertionError('compiled row lost a raw branch')
    return {'row': row, 'raw': raw, 'kept': kept,
            'mass': sum((BASE ** (-c['delta']) for c in kept), Fraction(0))}


def choose_row(rows):
    if not rows:
        return None, []
    compiled = [compile_row(rows, row) for row in rows]
    return min(compiled, key=lambda c: (c['mass'], c['row'])), compiled


def search(rows, budget, cache, stats):
    stats['calls'] += 1
    rows, forced, _ = dag.forced_closure(rows)
    delta = forced.bit_count()
    if delta > budget:
        return None
    left = budget - delta
    if not rows:
        return forced
    key = (rows, left)
    if key in cache:
        stats['cache_hits'] += 1
        result = cache[key]
        return None if result is None else forced | result
    stats['compiled_states'] += 1
    chosen, compiled = choose_row(rows)
    stats['row_candidates_compiled'] += len(compiled)
    stats['profiles'].append({'rows': rows, 'remaining_budget': left,
                              'chosen': chosen, 'all_rows': compiled})
    for child in chosen['kept']:
        if child['delta'] > left:
            continue
        result = search(child['rows'], left - child['delta'], cache, stats)
        if result is not None:
            cache[key] = child['cut_mask'] | result
            return forced | cache[key]
    cache[key] = None
    return None


def optimize_hitting(rows, budget):
    if not isinstance(budget, int) or isinstance(budget, bool) or budget < 0:
        raise ValueError('nonnegative integer budget required')
    rows = core.minimal_rows(rows)
    factors = core.incidence_factors(rows)
    remaining, chosen, attempts = budget, 0, []
    for index, factor in enumerate(factors):
        answer = None
        cache = {}
        for trial in range(remaining + 1):
            stats = {'factor': index, 'trial_budget': trial, 'calls': 0,
                     'compiled_states': 0, 'cache_hits': 0,
                     'row_candidates_compiled': 0, 'profiles': []}
            answer = search(factor, trial, cache, stats)
            stats['success'] = answer is not None
            attempts.append(stats)
            if answer is not None:
                if answer.bit_count() != trial:
                    raise AssertionError('first successful factor budget was not exact')
                chosen |= answer
                remaining -= trial
                break
        if answer is None:
            return {'status': 'BUDGET_FAILURE', 'factor_count': len(factors),
                    'completed_factors': index, 'spent': budget - remaining,
                    'failure_factor_lower_bound': remaining + 1, 'attempts': attempts,
                    'calls': sum(a['calls'] for a in attempts),
                    'compiled_states': sum(a['compiled_states'] for a in attempts)}
    if not all(chosen & h for h in rows):
        raise AssertionError('combined witness misses an original row')
    return {'status': 'SOLVED', 'cut_mask': chosen, 'cost': chosen.bit_count(),
            'factor_count': len(factors), 'attempts': attempts,
            'calls': sum(a['calls'] for a in attempts),
            'compiled_states': sum(a['compiled_states'] for a in attempts)}


def solve(source, target, budget):
    S, T = core.validate_input(source, target, budget)
    H = tuple(core.conflicts(S, T))
    answer = optimize_hitting(H, min(budget, max(0, len(S.labels) - 1)))
    answer['conflict_count'] = len(H)
    answer['minimal_conflict_count'] = len(core.minimal_rows(H))
    if answer['status'] == 'SOLVED':
        answer['certificate'] = core.certificate_for(S, T, answer['cut_mask'])
        if not core.verify_certificate(source, target, budget, answer['certificate']):
            raise AssertionError('original-source certificate rejected')
    return answer


def json_safe(value):
    if isinstance(value, Fraction):
        return {'numerator': value.numerator, 'denominator': value.denominator,
                'greater_than_one': value > 1}
    if isinstance(value, dict):
        return {k: json_safe(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [json_safe(v) for v in value]
    return value
