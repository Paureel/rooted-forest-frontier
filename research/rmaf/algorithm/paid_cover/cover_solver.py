#!/usr/bin/env python3
"""One-shot paid-cover candidate executable; universal formal proof remains OPEN.

Uses existing discovery graph primitives, not an optimum-oracle routine.
The fallback explicitly enumerates budgeted edge cut sets, validates each
result, and returns a witness. No local_candidates/opt/brute_completion calls.
"""
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import sys

CAMPAIGN = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(CAMPAIGN / 'pure_bridge'))
from check_geometry import Tree


def canon_parts(parts):
    return tuple(sorted(tuple(sorted(p)) for p in parts))


def cut_parts(source, cuts):
    cuts = {tuple(sorted(e)) for e in cuts}
    if not cuts <= set(source.edges):
        raise ValueError('nonexistent cut edge')
    unseen = set(source.adj)
    parts = []
    empty = []
    while unseen:
        v = min(unseen)
        region = {v}
        todo = [v]
        unseen.remove(v)
        for a in todo:
            for b in sorted(source.adj[a] & unseen):
                if tuple(sorted((a, b))) not in cuts:
                    unseen.remove(b)
                    region.add(b)
                    todo.append(b)
        labels = tuple(sorted(x for x, a in source.labels.items() if a in region))
        if labels:
            parts.append(labels)
        else:
            empty.append(sorted(region))
    return canon_parts(parts), empty


def parse_state(raw_target, raw_sources, q):
    if not isinstance(q, int) or isinstance(q, bool):
        raise ValueError('integer budget required')
    if q < 0:
        raise ValueError('negative budget')
    if raw_target is None:
        if raw_sources:
            raise ValueError('nonempty source for empty target')
        return None, []
    target = Tree(raw_target)
    sources = [Tree(s) for s in raw_sources]
    flat = [x for s in sources for x in s.labels]
    if len(flat) != len(set(flat)):
        raise ValueError('duplicate forest label')
    if set(flat) != set(target.labels):
        raise ValueError('missing/foreign forest label')
    return target, sources


def valid_partition(target, sources, parts):
    if target is None:
        return not parts and not sources
    flat = [x for b in parts for x in b]
    if any(not b for b in parts) or len(flat) != len(set(flat)) or set(flat) != set(target.labels):
        return False
    owners = []
    used_target = set()
    used_source = [set() for _ in sources]
    for block in parts:
        poss = [i for i, s in enumerate(sources) if set(block) <= set(s.labels)]
        if len(poss) != 1:
            return False
        i = poss[0]
        a, b = target.span(block), sources[i].span(block)
        if used_target & a or used_source[i] & b:
            return False
        if target.shape(block) != sources[i].shape(block):
            return False
        used_target.update(a)
        used_source[i].update(b)
        owners.append(i)
    return True


def membership(target, sources):
    if target is None:
        return dict(triple=True, pure=True, compatible=[], overlaps=[])
    good = [target.shape(s.labels) == s.shape(s.labels) for s in sources]
    spans = [target.span(s.labels) for s in sources]
    overlap = []
    pure = True
    for i, s in enumerate(spans):
        for j in range(i):
            shared = sorted(s & spans[j])
            for v in shared:
                degrees = [target.degree(v, spans[j]), target.degree(v, s)]
                if degrees != [2, 2]:
                    pure = False
                overlap.append(dict(colors=[j, i], vertex=v, degrees=degrees))
    return dict(triple=all(g or len(s.labels) == 3 for g, s in zip(good, sources)),
                pure=pure, compatible=good, overlaps=overlap)


def source_realization(source, parts, charge):
    parts = canon_parts(parts)
    for edges in combinations(source.edges, charge):
        got, empty = cut_parts(source, edges)
        if got == parts:
            return dict(edges=[list(e) for e in edges], empty_regions=empty)
    return None


def select_core(target, sources):
    mem = membership(target, sources)
    spans = [target.span(s.labels) for s in sources]
    for v in sorted(target.adj):
        touching = [i for i, span in enumerate(spans) if v in span]
        if len(touching) < 2:
            continue
        degrees = [target.degree(v, spans[i]) for i in touching]
        if 3 not in degrees or not all(mem['compatible'][i] for i in touching):
            continue
        plans = {}
        for i in touching:
            regions, _ = target.leaf_regions({v}, sources[i].labels)
            r = len(regions)
            if r not in (2, 3):
                return None
            realization = source_realization(sources[i], regions, r - 1)
            if realization is None:
                return None
            plans[i] = dict(parts=canon_parts(regions), charge=r - 1,
                            realization=realization)
        return dict(vertex=v, touching=touching, degrees=degrees, plans=plans)
    return None


def core_children(sources, core):
    children = []
    seen = set()
    for keep in core['touching']:
        raw = []
        history = []
        d = 0
        for i, source in enumerate(sources):
            if i not in core['plans'] or i == keep:
                raw.append(source.syntax)
            else:
                plan = core['plans'][i]
                raw.extend(source.shape(b) for b in plan['parts'])
                d += plan['charge']
                history.append(dict(color=i, source=source.syntax, **plan))
        key = canon_parts(Tree(s).labels for s in raw)
        if key in seen:
            continue
        seen.add(key)
        children.append(dict(retain=keep, charge=d, source=raw, history=history))
    return children


def fallback(target, sources, q, stats):
    """Explicit budgeted edge search; no optimum instrument used as a step."""
    edges = [(i, e) for i, s in enumerate(sources) for e in s.edges]
    for d in range(min(q, len(edges)) + 1):
        for chosen in combinations(edges, d):
            stats['fallback_cutsets'] += 1
            cuts = [[] for _ in sources]
            for i, e in chosen:
                cuts[i].append(e)
            parts = []
            for source, es in zip(sources, cuts):
                block, _ = cut_parts(source, es)
                parts.extend(block)
            if valid_partition(target, sources, parts):
                return dict(partition=[list(b) for b in canon_parts(parts)],
                            additional_cuts=len(parts) - len(sources),
                            fallback_edges=[[list(e) for e in es] for es in cuts])
    return None


def reconstruct_sources(sources, parts):
    """Extend disjoint minimal spans by deterministic multi-source BFS."""
    output = []
    for source in sources:
        blocks = [b for b in parts if set(b) <= set(source.labels)]
        owner = {}
        todo = []
        for i, block in enumerate(blocks):
            for v in sorted(source.span(block)):
                if v in owner:
                    raise ValueError('overlapping source spans in reconstruction')
                owner[v] = i
                todo.append(v)
        for u in todo:
            for v in sorted(source.adj[u]):
                if v not in owner:
                    owner[v] = owner[u]
                    todo.append(v)
        cuts = [e for e in source.edges if owner[e[0]] != owner[e[1]]]
        got, empty = cut_parts(source, cuts)
        if got != canon_parts(blocks) or empty or len(cuts) != len(blocks)-1:
            raise AssertionError('reconstruction mismatch')
        output.append(dict(source=source.syntax, cuts=[list(e) for e in cuts],
                           blocks=[list(b) for b in got]))
    return output


def solve(raw_target, raw_sources, q):
    target, initial = parse_state(raw_target, raw_sources, q)
    stats = dict(recursive_states=0, core_states=0, children_emitted=0,
                 fallback_cutsets=0, library_calls=0)
    ledger = []
    if target is None:
        return dict(feasible=True, partition=[], additional_cuts=0,
                    reconstruction=[], stats=stats, ledger=ledger)

    def visit(sources, budget):
        stats['recursive_states'] += 1
        current = [tuple(sorted(s.labels)) for s in sources]
        if valid_partition(target, sources, current):
            return dict(partition=[list(b) for b in canon_parts(current)],
                        additional_cuts=0, history=[])
        core = select_core(target, sources)
        if core is not None:
            stats['core_states'] += 1
            children = core_children(sources, core)
            stats['children_emitted'] += len(children)
            ledger.append(dict(kind='core', budget=budget, vertex=core['vertex'],
                               colors=core['touching'], costs=[x['charge'] for x in children]))
            for child in children:
                if child['charge'] > budget:
                    continue
                answer = visit([Tree(s) for s in child['source']], budget-child['charge'])
                if answer is not None:
                    return dict(partition=answer['partition'],
                                additional_cuts=child['charge']+answer['additional_cuts'],
                                history=[child['history'], answer.get('history', [])])
            return None
        mem = membership(target, sources)
        queries = []
        if mem['pure']:
            queries.append(dict(kind='first-unmarked-local-query',
                                source_component=0, labels=sorted(sources[0].labels),
                                additional_cut_budget=budget,
                                marked_regions=1, role_swap_budget=budget))
        ledger.append(dict(kind='fallback', budget=budget, membership=mem,
                           hypothetical_queries=queries,
                           disabled_reason='pure G1-G7 and triple G1-G3 open'))
        return fallback(target, sources, budget, stats)

    ans = visit(initial, q)
    if ans is None:
        return dict(feasible=False, stats=stats, ledger=ledger)
    if not valid_partition(target, initial, ans['partition']):
        raise AssertionError('returned witness invalid in original state')
    reconstruction = reconstruct_sources(initial, ans['partition'])
    actual = len(ans['partition']) - len(initial)
    if actual > q:
        raise AssertionError('budget overrun')
    return dict(feasible=True, partition=ans['partition'], additional_cuts=actual,
                reconstruction=reconstruction, stats=stats, ledger=ledger)


def mass(costs, base=Fraction(231, 100)):
    return sum((base ** -d for d in costs), Fraction())
