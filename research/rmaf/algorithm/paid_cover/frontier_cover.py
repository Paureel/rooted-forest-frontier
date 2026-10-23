#!/usr/bin/env python3
"""One-shot minimum-terminal-frontier experiment, not a certified safe cover.

The candidate's total action includes original-state cut-search fallback.
Only the measurement harness computes minimum budgets as test reference.
"""
from itertools import combinations
from pathlib import Path
import argparse
import hashlib
import json
import sys
import time
from cover_solver import (Tree, parse_state, cut_parts, canon_parts, membership,
                          solve, mass, reconstruct_sources)
from run_cover import controls as b1_controls

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'branching'))
from exact_search import trees, node


def frontier(target, sources, maxcuts=None, first_only=True):
    edges = [(i,e) for i,s in enumerate(sources) for e in s.edges]
    maxcuts = len(edges) if maxcuts is None else min(maxcuts, len(edges))
    states = []
    seen = set()
    tested = 0
    # first_only=False produces the all-terminal superset with every cut cost.
    for d in range(maxcuts+1):
        at_d = []
        for cut in combinations(edges,d):
            tested += 1
            by_color = [[] for _ in sources]
            for i,e in cut:
                by_color[i].append(e)
            parts = []
            raw = []
            for source, es in zip(sources,by_color):
                blocks,_ = cut_parts(source,es)
                parts.extend(blocks)
                raw.extend(source.shape(b) for b in blocks)
            key = canon_parts(parts)
            if key in seen:
                continue
            source_child = [Tree(s) for s in raw]
            if not membership(target,source_child)['triple']:
                continue
            # Drop redundant edge sets (including leafless cut regions) so
            # the charge always equals the actual increase in label blocks.
            if len(parts)-len(sources) != d:
                continue
            seen.add(key)
            at_d.append(dict(charge=d, partition=[list(b) for b in key], source=raw,
                             precuts=[[list(e) for e in es] for es in by_color]))
        states.extend(at_d)
        if at_d and first_only:
            break
    return dict(states=states, cutsets_tested=tested,
                minimum_paid=states[0]['charge'] if states else None)


def solve_frontier(raw_target, raw_sources, budget, include_fallback=True):
    target,sources = parse_state(raw_target,raw_sources,budget)
    if target is None:
        return dict(feasible=True, partition=[], additional_cuts=0, cover=[], fallback_used=False)
    cover = frontier(target,sources,maxcuts=budget)
    for child in cover['states']:
        ans = solve(raw_target,child['source'],budget-child['charge'])
        if ans['feasible']:
            return dict(feasible=True, partition=ans['partition'],
                        additional_cuts=child['charge']+ans['additional_cuts'],
                        reconstruction=reconstruct_sources(sources,ans['partition']),
                        cover=cover, fallback_used=False)
    if include_fallback:
        ans = solve(raw_target,raw_sources,budget)
        return dict(**ans, cover=cover, fallback_used=True)
    return dict(feasible=False, cover=cover, fallback_used=False)


def controls():
    prev = b1_controls()
    assert prev['passed'] == 27
    checks = ['B1-replay-27']
    target,sources = parse_state(((0,1),2),[((0,1),2)],0)
    f = frontier(target,sources)
    assert len(f['states']) == 1 and f['minimum_paid'] == 0
    checks.append('identical-triple-zero-frontier')
    target,sources = parse_state(((0,1),(2,3)),[((0,2),(1,3))],2)
    f = frontier(target,sources)
    assert len(f['states']) == 5 and f['minimum_paid'] == 1
    checks.append('quartet-five-one-cut-frontiers')
    value = mass([1]*5)
    assert str(value) == '500/231'
    checks.append('quartet-mass')
    caught = []
    try:
        assert value < 1
    except AssertionError:
        caught.append('false-mass-acceptance')
    literal = canon_parts([[0],[1,2,3]])
    keys = [canon_parts(s['partition']) for s in f['states']]
    assert literal in keys
    checks.append('literal-frontier-clean')
    try:
        assert literal in [k for k in keys if k != literal]
    except AssertionError:
        caught.append('deleted-literal-frontier')
    assert len(caught) == 2
    return dict(B1=prev, passed=len(checks)+len(caught), total=7,
                positive=checks, corruptions_caught=caught, quartet_cover=f)


def shape_reps(n):
    output = {}
    def shape(t):
        return 0 if isinstance(t,int) else node(shape(t[0]),shape(t[1]))
    ts = trees(tuple(range(n)))
    for t in ts:
        output.setdefault(repr(shape(t)),t)
    return tuple(output.values()),ts


def reference_minimum(t,u):
    """Test reference only. Not consulted by the frontier generator/solver."""
    n = len(Tree(t).labels)
    for q in range(n):
        answer = solve(t,[u],q)
        if answer['feasible']:
            return q,answer
    raise AssertionError('singleton upper bound failed')


def inspect_pair(t,u):
    q,reference = reference_minimum(t,u)
    answer = solve_frontier(t,[u],q,include_fallback=False)
    if answer['feasible']:
        return dict(failed=False, n=len(Tree(t).labels), q=q,
                    minimum_paid=answer['cover']['minimum_paid'],
                    states=len(answer['cover']['states']), cutsets=answer['cover']['cutsets_tested'])
    child_rows = []
    for child in answer['cover']['states']:
        for local in range(len(Tree(t).labels)):
            ans = solve(t,child['source'],local)
            if ans['feasible']:
                child_rows.append(dict(**child, residual_optimum=local,
                                       paid_total=local+child['charge'], witness=ans['partition']))
                break
    total = solve_frontier(t,[u],q,include_fallback=True)
    assert total['feasible'] and total['fallback_used']
    return dict(failed=True, n=len(Tree(t).labels), target=t, source=[u],
                optimum_cuts=q, minimum_paid=answer['cover']['minimum_paid'],
                reference=reference, children=child_rows,
                cover=answer['cover'], total_fallback=total,
                verdict='minimum-paid-terminal-cover-discards-every-optimum')


def run(stage):
    start = time.perf_counter()
    if stage == 'controls':
        return controls()
    rows = []
    count = 0
    for n in (4,5,6):
        reps,ts = shape_reps(n)
        limit = {4:7,5:7,6:6}[n] if stage == 'pilot' else None
        at_n = 0
        for t in reps:
            for u in ts:
                if limit is not None and at_n >= limit:
                    break
                before = time.perf_counter()
                row = inspect_pair(t,u)
                row['elapsed_seconds'] = time.perf_counter()-before
                count += 1
                at_n += 1
                rows.append(row)
                if row['failed']:
                    return dict(status='FIRE', pairs=count, rows=rows, witness=row,
                                elapsed_seconds=time.perf_counter()-start,
                                smallest_scope='First failure in increasing n, then deterministic shape-representative/tree order; lower leaf counts in this bounded family exhausted.')
            if limit is not None and at_n >= limit:
                break
    return dict(status='NO-FIRE', pairs=count, rows=rows,
                elapsed_seconds=time.perf_counter()-start,
                finite_scope='No universal coverage claim; all values are development checks.')


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--stage',choices=['controls','pilot','bounded'],required=True)
    a = p.parse_args()
    start = time.perf_counter()
    result = run(a.stage)
    if a.stage == 'controls':
        assert result['passed'] == result['total']
    report = dict(stage=a.stage,result=result, elapsed_seconds=time.perf_counter()-start,
                  hashes={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in
                          [Path(__file__),Path(__file__).with_name('PIN-v2.md'),Path(__file__).with_name('cover_solver.py')]},
                  provenance='Same-author development; graph primitives and exact reference share representation. No independent certification.')
    dest = ROOT/'results'/f'algorithm-cover-frontier-{a.stage}-v2.json'
    if dest.exists():
        raise FileExistsError(str(dest))
    dest.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(output=str(dest),stage=a.stage,status=result.get('status'),
                         pairs=result.get('pairs'),passed=result.get('passed'),
                         elapsed_seconds=report['elapsed_seconds'])))


if __name__ == '__main__':
    main()
