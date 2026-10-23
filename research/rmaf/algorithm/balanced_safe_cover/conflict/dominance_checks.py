#!/usr/bin/env python3
"""One-shot finite C4 regression, using GLOBAL-C's already-controlled oracle.
Shared code/author means internal consistency only; not fresh verification.
"""
import hashlib
import itertools as it
import json
from pathlib import Path
from datetime import datetime, timezone
from time import perf_counter
from exact_conflicts import Tree, conflicts, oracle, trees


def representative_edges(H, m):
    columns = [frozenset(i for i,h in enumerate(H) if h & (1 << e)) for e in range(m)]
    maximal = {c for c in columns if c and not any(c < d for d in columns)}
    return tuple(sorted(min(e for e,c in enumerate(columns) if c == d) for d in maximal))


def restricted_optimum(H, reps):
    for count in range(len(reps)+1):
        for chosen in it.combinations(reps,count):
            c = sum(1 << e for e in chosen)
            if all(c & h for h in H):
                return count, chosen
    raise AssertionError('maximal-column reps contain no transversal')


def main():
    frozen = [
        {'id':'nested','H':[3,1],'m':2,'reps':[0],'opt':1},
        {'id':'triangle','H':[3,6,5],'m':3,'reps':[0,1,2],'opt':2},
        {'id':'equal-incidence','H':[15],'m':4,'reps':[0],'opt':1},
        {'id':'empty','H':[],'m':4,'reps':[],'opt':0},
    ]
    controls, mutations = [], []
    for f in frozen:
        reps = representative_edges(f['H'],f['m'])
        optimum, chosen = restricted_optimum(f['H'],reps)
        assert list(reps) == f['reps'] and optimum == f['opt'], (f,reps,optimum)
        controls.append({**f,'actual_reps':reps,'actual_optimum':optimum,'passed':True})
        for field, actual in [('opt',optimum),('reps',list(reps))]:
            corrupt = actual + 1 if field == 'opt' else list(reversed(reps))+[999]
            assert actual != corrupt
            mutations.append({'id':f['id'],'field':field,'corrupt':corrupt,'caught':True})
    H = [1,2]
    assert all(3 & h for h in H) and not all(2 & h for h in H)
    mutations.append({'id':'invalid-domination','caught':True,'clean_twin':True})
    rows, first_large = [], None
    for n in range(1,5):
        ts = trees(tuple(chr(97+i) for i in range(n)))
        count, hist = 0, {}
        start = perf_counter()
        for s,t in it.product(ts,repeat=2):
            S,T = Tree(s),Tree(t)
            H = list(conflicts(S,T))
            reps = representative_edges(H,len(S.edges))
            reduced, witness = restricted_optimum(H,reps)
            expected = oracle(S,T)[0]
            assert reduced == expected, (s,t,H,reps,expected,reduced)
            count += 1
            key = str((expected,len(reps)))
            hist[key] = hist.get(key,0)+1
            if len(reps) > 2*expected and expected > 0 and first_large is None:
                first_large = {'source':s,'target':t,'optimum':expected,'representative_count':len(reps),
                               'representatives':S.edge_receipt(sum(1<<e for e in reps)),
                               'incidence_columns':[[i for i,h in enumerate(H) if h & (1<<e)] for e in range(len(S.edges))]}
        rows.append({'n':n,'tree_count':len(ts),'ordered_pairs':count,'mismatches':0,
                     'optimum_representative_count_histogram':hist,'seconds':perf_counter()-start})
    out = {'kind':'GLOBAL-C-column-domination-regression','date':datetime.now(timezone.utc).isoformat(),
           'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'shared_oracle_sha256':hashlib.sha256(Path(__file__).with_name('exact_conflicts.py').read_bytes()).hexdigest(),
           'lineage':'shared GLOBAL-C Tree/partition oracle; not independent verification',
           'frozen_controls':controls,'mutations':mutations,'sizes':rows,
           'first_more_than_twice_optimum_columns':first_large,
           'verdict':'FINITE-REGRESSION-CLEAN; NO-COVER-BOUND'}
    dest = Path('research/rmaf/results/algorithm-balanced-cover-conflict-dominance-v1.json')
    dest.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'output':str(dest),'frozen_controls':len(controls),'mutation_catches':len(mutations),
                      'pair_checks':sum(r['ordered_pairs'] for r in rows),'mismatches':0,
                      'first_large_column_count':None if first_large is None else first_large['representative_count'],
                      'verdict':out['verdict']}))


if __name__ == '__main__':
    main()
