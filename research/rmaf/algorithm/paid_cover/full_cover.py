#!/usr/bin/env python3
"""One-shot all-minimal-terminal safe-cover candidate; formal obligations OPEN.

All generation, discarded states, local budgets and source reconstruction are
retained. Conditional polynomial terminal libraries remain disabled.
"""
from pathlib import Path
from fractions import Fraction
import json
import hashlib
import time
from cover_solver import (parse_state, solve, valid_partition, mass,
                          reconstruct_sources, canon_parts, Tree)
from frontier_cover import frontier, controls as previous_controls

ROOT = Path(__file__).resolve().parents[2]


def refines(parts, coarse):
    return all(any(set(b) <= set(c) for c in coarse) for b in parts)


def full_minimal_cover(target, sources, budget):
    generated = frontier(target,sources,maxcuts=budget,first_only=False)
    allstates = generated['states']
    retained = []
    scans = 0
    for s in allstates:
        dominated = False
        for r in allstates:
            scans += 1
            if r['charge'] < s['charge'] and refines(s['partition'],r['partition']):
                dominated = True
                break
        if not dominated:
            retained.append(s)
    return dict(states=retained, prefilter_states=len(allstates),
                cutsets_tested=generated['cutsets_tested'],coarsening_scans=scans,
                paid_vector=[s['charge'] for s in retained],
                exact_mass=str(mass(s['charge'] for s in retained)))


def solve_full(raw_target, raw_sources, budget):
    target,sources = parse_state(raw_target,raw_sources,budget)
    if target is None:
        return dict(feasible=True,partition=[],additional_cuts=0,cover={},queries=[],fallback_used=False)
    cover = full_minimal_cover(target,sources,budget)
    queries = []
    for child in cover['states']:
        remaining = budget-child['charge']
        ans = solve(raw_target,child['source'],remaining)
        queries.append(dict(precuts=child['precuts'],child_blocks=child['partition'],
                            paid=child['charge'],remaining_budget=remaining,
                            algorithm='explicit finite budgeted completion; libraries disabled',
                            feasible=ans['feasible'],stats=ans['stats']))
        if ans['feasible']:
            assert valid_partition(target,sources,ans['partition'])
            return dict(feasible=True,partition=ans['partition'],
                        additional_cuts=len(ans['partition'])-len(sources),
                        reconstruction=reconstruct_sources(sources,ans['partition']),
                        cover=cover,queries=queries,fallback_used=False)
    ans = solve(raw_target,raw_sources,budget)
    return dict(**ans,cover=cover,queries=queries,fallback_used=True)


def main():
    started = time.perf_counter()
    prev = previous_controls()
    assert prev['passed'] == 7 and prev['B1']['passed'] == 27
    quartet = solve_full(((0,1),(2,3)),[((0,2),(1,3))],2)
    assert len(quartet['cover']['states']) == 5
    assert quartet['cover']['paid_vector'] == [1]*5
    assert quartet['cover']['exact_mass'] == '500/231'
    assert quartet['feasible'] and quartet['additional_cuts'] == 2 and not quartet['fallback_used']
    target = ((((3,4),2),1),0)
    source = (((1,4),2),(0,3))
    full = solve_full(target,[source],2)
    literal = canon_parts([[0,1,4],[2],[3]])
    keep = [s for s in full['cover']['states'] if refines(literal,s['partition'])]
    assert keep and full['feasible'] and full['additional_cuts'] == 2 and not full['fallback_used']
    corrupted = [s for s in full['cover']['states'] if not refines(literal,s['partition'])]
    caught = False
    try:
        assert any(refines(literal,s['partition']) for s in corrupted)
    except AssertionError:
        caught = True
    assert caught
    report = dict(status='complete-enumerative-candidate-no-improved-exponent',
                  controls=dict(previous=prev,positive=5,total=6,corruption_caught=caught),
                  quartet=quartet,five_leaf_failed_minimum_cover_repaired=full,
                  literal_parent_witness=[list(b) for b in literal],
                  literal_coarsening_cover_states=keep,
                  elapsed_seconds=time.perf_counter()-started,
                  hashes={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in
                          [Path(__file__),Path(__file__).with_name('PIN-v3.md'),
                           Path(__file__).with_name('frontier_cover.py'),Path(__file__).with_name('cover_solver.py')]},
                  proof_scope='Universal coverage/restriction correspondence OPEN; explicit original fallback remains; no untouched-input or separate-author certification.')
    dest = ROOT/'results'/'algorithm-cover-full-pilot-v3.json'
    assert not dest.exists(),dest
    dest.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(output=str(dest),status=report['status'],
                         five_leaf_vector=full['cover']['paid_vector'],
                         five_leaf_mass=full['cover']['exact_mass'],
                         cutsets=full['cover']['cutsets_tested'],
                         prefilter_states=full['cover']['prefilter_states'],
                         retained=len(full['cover']['states']),
                         fallback_used=full['fallback_used'],elapsed_seconds=report['elapsed_seconds'])))


if __name__ == '__main__':
    main()
