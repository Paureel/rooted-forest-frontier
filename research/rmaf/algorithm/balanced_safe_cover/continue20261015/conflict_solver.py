#!/usr/bin/env python3
"""One-shot GLOBAL-CB1 paid exact proposal, with no smaller-base claim.

Reuses the frozen GLOBAL-C polynomial tree/conflict primitives. No partition,
cutset, local-distance, or packing oracle is called by solve/optimize_hitting.
See SPEC-CB1.md and README.md for charged scope and required checks.
"""
from __future__ import annotations
import sys
from pathlib import Path

CONFLICT_DIR = Path(__file__).resolve().parents[1] / 'conflict'
if str(CONFLICT_DIR) not in sys.path:
    sys.path.insert(0, str(CONFLICT_DIR))
from exact_conflicts import Tree, conflicts, agreement


def minimal_rows(rows):
    """Remove duplicate rows and rows containing another row."""
    rows = tuple(sorted(set(rows), key=lambda h: (h.bit_count(), h)))
    kept = []
    for h in rows:
        if h <= 0:
            raise ValueError('conflict rows must be nonempty bit masks')
        if not any(h & q == q for q in kept):
            kept.append(h)
    return tuple(sorted(kept))


def incidence_factors(rows):
    """Partition rows into components with disjoint original-edge universes."""
    pending = list(minimal_rows(rows))
    factors = []
    while pending:
        selected = [pending.pop(0)]
        universe = selected[0]
        while True:
            touching = [h for h in pending if h & universe]
            if not touching:
                break
            for h in touching:
                pending.remove(h)
                selected.append(h)
                universe |= h
        factors.append(tuple(sorted(selected)))
    return tuple(sorted(factors, key=lambda f: min(e for h in f for e in bits(h))))


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def quotient_rows(rows):
    """C4: keep one canonical edge of every maximal nonempty incidence class."""
    rows = minimal_rows(rows)
    universe = 0
    for h in rows:
        universe |= h
    edge_column = {e: sum(1 << i for i, h in enumerate(rows) if h & (1 << e))
                   for e in bits(universe)}
    classes = {}
    for e, column in edge_column.items():
        classes.setdefault(column, e)
    maximal = [column for column in classes
               if not any(column != other and column & other == column
                          for other in classes)]
    retained = sum(1 << classes[column] for column in maximal)
    projected = tuple(h & retained for h in rows)
    if any(h == 0 for h in projected):
        raise AssertionError('maximal incidence projection lost an entire row')
    return minimal_rows(projected)


def bounded_search(rows, budget, stats, selected=0):
    """Search a single root factor. Every failed branch is counted."""
    stats['nodes'] += 1
    stats['max_depth'] = max(stats['max_depth'], stats['initial_budget'] - budget)
    if not rows:
        return selected
    if budget == 0:
        return None
    reduced = quotient_rows(rows)
    row = min(reduced, key=lambda h: (h.bit_count(), h))
    rank = row.bit_count()
    stats['max_branch_rank'] = max(stats['max_branch_rank'], rank)
    stats['branch_rank_histogram'][str(rank)] = stats['branch_rank_histogram'].get(str(rank), 0) + 1
    for e in bits(row):
        bit = 1 << e
        next_rows = tuple(h for h in reduced if not h & bit)
        answer = bounded_search(next_rows, budget - 1, stats, selected | bit)
        if answer is not None:
            return answer
    return None


def optimize_hitting(rows, budget):
    """Find one minimum transversal at cost<=budget, or prove budget failure.

    Root factors are optimized independently, avoiding Cartesian products of
    alternative witnesses. SEARCH itself is explicit bounded enumeration.
    """
    if not isinstance(budget, int) or isinstance(budget, bool) or budget < 0:
        raise ValueError('nonnegative integer budget required')
    rows = minimal_rows(rows)
    factors = incidence_factors(rows)
    remaining, chosen, attempts = budget, 0, []
    for index, factor in enumerate(factors):
        answer = None
        for trial in range(remaining + 1):
            stats = {'factor': index, 'trial_budget': trial, 'initial_budget': trial,
                     'nodes': 0, 'max_depth': 0, 'max_branch_rank': 0,
                     'branch_rank_histogram': {}}
            answer = bounded_search(factor, trial, stats)
            stats['success'] = answer is not None
            attempts.append(stats)
            if answer is not None:
                if answer.bit_count() != trial:
                    raise AssertionError('first successful budget was not exact')
                chosen |= answer
                remaining -= trial
                break
        if answer is None:
            return {'status': 'BUDGET_FAILURE', 'factor_count': len(factors),
                    'completed_factors': index, 'spent': budget - remaining,
                    'failure_factor_lower_bound': remaining + 1, 'attempts': attempts,
                    'nodes': sum(a['nodes'] for a in attempts)}
    if not all(chosen & h for h in rows):
        raise AssertionError('combined factor witness misses an original row')
    return {'status': 'SOLVED', 'cut_mask': chosen, 'cost': chosen.bit_count(),
            'factor_count': len(factors), 'attempts': attempts,
            'nodes': sum(a['nodes'] for a in attempts),
            'max_branch_rank': max((a['max_branch_rank'] for a in attempts), default=0)}


def validate_input(source, target, budget):
    if not isinstance(budget, int) or isinstance(budget, bool) or budget < 0:
        raise ValueError('nonnegative integer budget required')
    def check(tree):
        seen = set()
        def walk(node):
            if isinstance(node, str):
                if node in seen:
                    raise ValueError('duplicate original label')
                seen.add(node)
                return node
            if not isinstance(node, (tuple, list)) or len(node) != 2:
                raise ValueError('binary syntax and original string labels required')
            return walk(node[0]), walk(node[1])
        return None if tree is None else walk(tree), seen
    s, a = check(source)
    t, b = check(target)
    if a != b:
        raise ValueError('equal original label sets required')
    return Tree(s), Tree(t)


def json_tree(tree):
    return list(map(json_tree, tree)) if isinstance(tree, tuple) else tree


def certificate_for(S, T, cut_mask):
    if cut_mask < 0 or cut_mask >> len(S.edges):
        raise ValueError('cut is not an original source edge')
    neighbors = {v: [] for v in S.parent}
    for i, (u, v) in enumerate(S.edges):
        if not cut_mask & (1 << i):
            neighbors[u].append(v)
            neighbors[v].append(u)
    reverse = {v: a for a, v in S.leaf.items()}
    unseen = set(S.parent)
    components = []
    while unseen:
        first = min(unseen)
        stack = [first]
        unseen.remove(first)
        vertices = []
        while stack:
            v = stack.pop()
            vertices.append(v)
            for w in neighbors[v]:
                if w in unseen:
                    unseen.remove(w)
                    stack.append(w)
        labels = sorted(reverse[v] for v in vertices if v in reverse)
        if not labels:
            raise ValueError('redundant cuts created an empty source component')
        components.append({'original_labels': labels,
                           'full_original_vertices': sorted(vertices),
                           'source_restriction': json_tree(S.restrict(labels)),
                           'target_support': sorted(T.support(labels))})
    components.sort(key=lambda c: c['original_labels'])
    partition = tuple(tuple(c['original_labels']) for c in components)
    if not agreement(S, T, partition):
        raise ValueError('original cut partition is not an agreement forest')
    r = cut_mask.bit_count()
    if S.labels and len(components) != r + 1:
        raise ValueError('nonredundant source component accounting failed')
    if not S.labels and (r or components):
        raise ValueError('empty input accounting failed')
    return {'original_source_edge_indices': list(bits(cut_mask)),
            'original_source_edges': [list(S.edges[e]) for e in bits(cut_mask)],
            'precut_cost': r, 'residual_cost': 0, 'total_cost': r,
            'terminal_class': 'all-compatible', 'original_unmarked_tau': 0,
            'components': components}


def verify_certificate(source, target, budget, certificate):
    try:
        S, T = validate_input(source, target, budget)
        edges = certificate['original_source_edge_indices']
        if any(not isinstance(e, int) or isinstance(e, bool) or e < 0 or e >= len(S.edges)
               for e in edges):
            return False
        if len(set(edges)) != len(edges) or len(edges) > budget:
            return False
        expected = certificate_for(S, T, sum(1 << e for e in edges))
        return certificate == expected
    except (ValueError, KeyError, TypeError):
        return False


def solve(source, target, budget):
    """Total ordinary-pair decision/minimum witness up to the supplied budget.

    Correctness uses C1 and normalization; each successful witness is checked
    directly. Generic worst-case cost remains unlicensed.
    """
    S, T = validate_input(source, target, budget)
    H = tuple(conflicts(S, T))
    cap = min(budget, max(0, len(S.labels) - 1))
    result = optimize_hitting(H, cap)
    result['conflict_count'] = len(H)
    result['minimal_conflict_count'] = len(minimal_rows(H))
    if result['status'] == 'SOLVED':
        result['certificate'] = certificate_for(S, T, result['cut_mask'])
        if not verify_certificate(source, target, budget, result['certificate']):
            raise AssertionError('full original-source certificate rejected')
    return result
