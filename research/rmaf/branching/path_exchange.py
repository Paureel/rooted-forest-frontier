#!/usr/bin/env python3
"""Problem-specific falsifier for a quantified overlap-path exchange lemma.

Uses this route's own exact evaluator, never another route's code. It tests
all optimal forests within a prescribed Whidden two-cut child, before free
tidying. A positive finite outcome cannot establish the universal lemma.
"""
from itertools import product
from pathlib import Path
import argparse
import json
import time
from exact_search import (trees, node, baseline_hard_pair, leaves, cherries,
                          offpath, embedding, all_partitions, valid)


def edges_of_embedding(tree, block):
    vertices = embedding(tree, block)
    return {v for v in vertices if v and v[:-1] in vertices}


def refining(partition, blocks):
    return all(any(frozenset(p) <= b for b in blocks) for p in partition)


def optimum_refinement(tree, other, blocks):
    best = len(leaves(tree))
    accepted = []
    for p in all_partitions(tuple(sorted(leaves(tree)))):
        if len(p) > best:
            break
        if refining(p, blocks) and valid(tree, other, p):
            best = len(p)
            accepted.append(p)
    assert accepted
    return best, accepted


def avoids(tree, partition, block, edge):
    return all(edge not in edges_of_embedding(tree, frozenset(p))
               for p in partition if frozenset(p) <= block)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--n', type=int, default=7)
    args = parser.parse_args()
    start = time.monotonic()
    ts = trees(tuple(range(args.n)))
    def shape(t):
        return 0 if isinstance(t, int) else node(shape(t[0]), shape(t[1]))
    reps = {}
    for t in ts:
        reps.setdefault(repr(shape(t)), t)
    tree_pairs = 0
    tested_states = 0
    path_states = 0
    counterexample = None
    for t in reps.values():
        for u in ts:
            tree_pairs += 1
            if not baseline_hard_pair(t, u):
                continue
            for x, y in ((t, u), (u, t)):
                for a, b in cherries(x):
                    sides = [frozenset(s) for s in offpath(y, a, b)]
                    blocks = sides + [leaves(x) - sides[0] - sides[1]]
                    tested_states += 1
                    es = [edges_of_embedding(x, z) for z in blocks]
                    overlap = {(i,j): es[i] & es[j] for i in range(3) for j in range(i)}
                    pairs = [pair for pair, common in overlap.items() if common]
                    if len(pairs) != 2:
                        continue
                    middle = set(pairs[0]) & set(pairs[1])
                    assert len(middle) == 1
                    bi = middle.pop()
                    ai, ci = [i for i in range(3) if i != bi]
                    ea = es[ai] & es[bi]
                    ec = es[ci] & es[bi]
                    assert not (es[ai] & es[ci])
                    path_states += 1
                    k, forests = optimum_refinement(x, y, blocks)
                    edge_pair_survives = []
                    for e, f in product(ea, ec):
                        surviving = [p for p in forests
                                     if ((avoids(x,p,blocks[bi],e) and avoids(x,p,blocks[bi],f))
                                         or (avoids(x,p,blocks[ai],e) and avoids(x,p,blocks[ci],f)))]
                        if surviving:
                            edge_pair_survives.append([e, f])
                    if not edge_pair_survives and counterexample is None:
                        counterexample = {'T': x, 'Tprime': y, 'cherry': [a,b],
                                          'blocks': [sorted(block) for block in blocks],
                                          'A_index': ai, 'B_index': bi, 'C_index': ci,
                                          'AB_edges': list(ea), 'BC_edges': list(ec),
                                          'optimum_components': k, 'optimal_forests': forests,
                                          'scope': 'Every choice of overlap edge pair fails the proposed exchange.'}
    result = {'n':args.n, 'tree_pairs_checked':tree_pairs,
              'eligible_whidden_states':tested_states, 'path_overlap_states':path_states,
              'counterexample':counterexample,'elapsed_seconds':time.monotonic()-start,
              'scope':'Finite falsification only, uncollapsed common cherry in child.'}
    output=Path(__file__).parents[1]/'results'/f'branching-path-exchange-n{args.n}.json'
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='counterexample'},indent=2))
    print('exchange refuted',counterexample is not None)


if __name__=='__main__':
    main()
