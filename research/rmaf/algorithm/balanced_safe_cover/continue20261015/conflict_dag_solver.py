#!/usr/bin/env python3
"""One-shot GLOBAL-CB2 paid residual-CNF/DAG proposal, no global base claim.

Wraps CB1's frozen polynomial primitives and certificate verifier. No optimizer
oracle or local distance call occurs; explicit search is charged in the trace.
"""
from __future__ import annotations
import conflict_solver as core


def forced_closure(rows):
    selected = 0
    steps = []
    while rows:
        rows = core.quotient_rows(rows)
        row = min(rows, key=lambda h: (h.bit_count(), h))
        if row.bit_count() != 1:
            break
        edge = next(core.bits(row))
        steps.append({'edge': edge, 'rows_before': list(rows)})
        selected |= row
        rows = tuple(h for h in rows if not h & row)
    return tuple(rows), selected, steps


def implies(stronger, weaker):
    """Every transversal of stronger hits weaker, by monotone-CNF subsumption."""
    return all(any(g & h == g for g in stronger) for h in weaker)


def dominates(left, right):
    return left['delta'] <= right['delta'] and implies(right['rows'], left['rows'])


def compile_children(rows):
    """Polynomial structural compilation. Input has no forced singleton row."""
    if not rows:
        return [], []
    row = min(rows, key=lambda h: (h.bit_count(), h))
    raw = []
    for e in core.bits(row):
        bit = 1 << e
        residual, forced, steps = forced_closure(tuple(h for h in rows if not h & bit))
        cuts = bit | forced
        raw.append({'branch_edge': e, 'rows': residual, 'cut_mask': cuts,
                    'delta': cuts.bit_count(), 'forcing_steps': steps})
    kept = []
    for candidate in sorted(raw, key=lambda c: (c['delta'], c['cut_mask'])):
        if any(dominates(other, candidate) for other in kept):
            continue
        kept = [other for other in kept if not dominates(candidate, other)]
        kept.append(candidate)
    if not kept:
        raise AssertionError('nonempty branch has no retained representative')
    # Every discarded raw branch is explicitly covered by a retained one.
    if not all(any(dominates(k, child) for k in kept) for child in raw):
        raise AssertionError('child dominance failed transitive coverage')
    return raw, kept


def verify_compilation(rows, raw, kept):
    return (raw, kept) == compile_children(rows)


def search(rows, budget, cache, stats):
    stats['calls'] += 1
    rows, forced, steps = forced_closure(rows)
    forced_cost = forced.bit_count()
    stats['forced_closure_edges'] += forced_cost
    if forced_cost > budget:
        return None
    left = budget - forced_cost
    if not rows:
        return forced
    key = (rows, left)
    if key in cache:
        stats['cache_hits'] += 1
        result = cache[key]
        return None if result is None else forced | result
    stats['compiled_states'] += 1
    raw, kept = compile_children(rows)
    stats['raw_children'] += len(raw)
    stats['retained_children'] += len(kept)
    stats['max_retained_children'] = max(stats['max_retained_children'], len(kept))
    stats['profiles'].append({'rows': rows, 'remaining_budget': left,
                              'raw': raw, 'kept': kept})
    for child in kept:
        if child['delta'] > left:
            stats['children_pruned_by_budget'] += 1
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
                     'forced_closure_edges': 0, 'cache_hits': 0, 'compiled_states': 0,
                     'raw_children': 0, 'retained_children': 0, 'max_retained_children': 0,
                     'children_pruned_by_budget': 0, 'profiles': []}
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
                    'failure_factor_lower_bound': remaining + 1,
                    'attempts': attempts,
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
