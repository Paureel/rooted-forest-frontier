#!/usr/bin/env python3
"""One-shot actual SlowCover control replay in the existing independent review.

Expected partitions come only from the previously frozen IndependentEdges
instrument. SlowCover is imported solely as the code under test. This adapter
is post-candidate review code, not an independent theorem or new replication.
"""
import copy
import hashlib
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[5]
ALG = ROOT / 'research/rmaf/algorithm'
sys.path.insert(0, str(ALG / 'balanced_safe_cover/verify'))
from IndependentEdges import Raw, score, blockkey
from ReplayWitnesses import raw_components
sys.path.insert(0, str(ALG / 'balanced_safe_cover/quotient'))
from SlowCover import generate_slow, decide_slow, verify_certificate

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def independent_certificate(s, t, cert):
    S, T = Raw(s), Raw(t)
    # Candidate addresses are integer preorder IDs; the independent instrument
    # uses strings. Compare actual cut-induced blocks after converting only
    # the address presentation, never using candidate cut/shape predicates.
    ordered = list(S.children)
    edges = [tuple(ordered[i] for i in e) for e in cert['original_source_edges']]
    assert all(e in S.edges for e in edges)
    got = blockkey(x['original_labels'] for x in cert['components'])
    realized = [p for p, choices in S.edge_partitions().items()
                if any(set(cut) == set(edges) for cut in choices)]
    assert realized == [got]
    assert len(edges) == len(got) - 1 == cert['total_cost'] == cert['precut_cost']
    assert cert['residual_cost'] == 0
    components = raw_components(S, edges)
    target_ordered = list(T.children)
    for record in cert['components']:
        labels = set(record['original_labels'])
        actual_vertices = {ordered[i] for i in record['full_original_vertices']}
        expected_vertices = next(c for c in components
                                 if {x for x,v in S.leaf.items() if v in c} == labels)
        assert actual_vertices == expected_vertices
        assert {target_ordered[i] for i in record['target_support']} == T.support(labels)
        assert Raw(record['source_restriction']).restriction(labels) == S.restriction(labels) == T.restriction(labels)
    # Independent score supplies all true optimum partitions below, and these
    # fixtures use the optimum budget, so every emitted partition must be one.
    return got

cases = [('singleton', 'a', 'a', 0, 0, 1),
         ('identical', [['a','b'],['c','d']], [['a','b'],['c','d']], 0, 0, 1),
         ('bad-triple', [['a','c'],'b'], [['a','b'],'c'], 1, 1, 3),
         ('crossing', [['a','c'],['b','d']], [['a','b'],['c','d']], 2, 2, 6)]

start = time.perf_counter()
plant = next(generate_slow('a', 'a', 0))
assert verify_certificate('a', 'a', 0, plant)
bad = copy.deepcopy(plant)
bad['total_cost'] = 1
assert not verify_certificate('a', 'a', 0, bad)
pilot = time.perf_counter() - start
rows = []
for name, s, t, budget, expected, distinct in cases:
    before = time.perf_counter()
    independent = score(s, t)
    assert independent['optimum_cuts'] == expected
    certificates = list(generate_slow(s, t, budget))
    best = decide_slow(s, t, budget)
    assert best is not None and best['total_cost'] == expected
    keys = set()
    mutations = []
    for cert in certificates:
        assert verify_certificate(s, t, budget, cert)
        keys.add(independent_certificate(s, t, cert))
        mutant = copy.deepcopy(cert)
        mutant['total_cost'] += 1
        assert not verify_certificate(s, t, budget, mutant)
        mutations.append({'claimed_total': mutant['total_cost'],
                          'actual_total': cert['total_cost'], 'caught': True})
    expected_keys = {blockkey(p) for p in independent['optimum_partitions']}
    assert keys == expected_keys and len(keys) == distinct
    if budget:
        assert decide_slow(s, t, budget - 1) is None
    rows.append(dict(id=name, source=s, target=t, budget=budget,
                     independent=independent, certificates=certificates,
                     certificate_realizations=len(certificates),
                     distinct_optimum_partitions=len(keys), cost_corruptions=mutations,
                     elapsed_seconds=time.perf_counter()-before, passed=True))

receipt = {'review_type': 'continued frozen independent review; actual slow source finite replay',
           'scope': 'four saved control cases only; no arbitrary-depth or universal algorithm theorem',
           'plant': {'known_singleton_recovered': True, 'corrupted_cost_caught': True,
                     'clean_twin_passed': True, 'pilot_seconds': pilot},
           'rows': rows, 'elapsed_seconds': time.perf_counter()-start,
           'source_hashes': {str(p.relative_to(ROOT)): sha(p) for p in
                             [Path(__file__), ALG/'balanced_safe_cover/verify/IndependentEdges.py',
                              ALG/'balanced_safe_cover/quotient/SlowCover.py',
                              ALG/'balanced_safe_cover/quotient/quotient_probe.py']},
           'lineage': 'shared mathematical definition and Python runtime; expected route imports no candidate code; this adapter intentionally invokes candidate under test'}
out = ROOT / 'research/rmaf/results/algorithm-review-continue-slow-source-replay.json'
assert not out.exists()
out.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({'cases': len(rows), 'passed': sum(x['passed'] for x in rows),
                  'seconds': receipt['elapsed_seconds'],
                  'realizations': [x['certificate_realizations'] for x in rows],
                  'partitions': [x['distinct_optimum_partitions'] for x in rows]}))
