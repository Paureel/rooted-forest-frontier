#!/usr/bin/env python3
"""Falsify path exchange on synthetic three-component forest states.

These states are not asserted reachable from the baseline algorithm. Fixed
blocks A={0,1}, B={2,3,4}, C={5,6}; A,C are homeomorphic, B is not.
The hypothesis is frozen before search: there exists an overlap-edge pair
for which an optimal refinement avoids both in B, or avoids them in A,C.
"""
from pathlib import Path
from itertools import product
import argparse
import json
import time
from exact_search import trees, node, restrict
from path_exchange import edges_of_embedding, optimum_refinement, avoids


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--limit',type=int,default=0)
    args=parser.parse_args()
    start=time.monotonic()
    blocks=[frozenset((0,1)),frozenset((2,3,4)),frozenset((5,6))]
    ts=trees(tuple(range(7)))
    if args.limit:
        stride=max(1,len(ts)//args.limit)
        ts=ts[::stride][:args.limit]
    total=0
    path_count=0
    instance_count=0
    witness=None
    for t in ts:
        total+=1
        es=[edges_of_embedding(t,z) for z in blocks]
        ea,ec=es[0]&es[1],es[1]&es[2]
        if not ea or not ec or (es[0]&es[2]):
            continue
        path_count+=1
        for middle in trees((2,3,4)):
            if restrict(t,blocks[1])==middle:
                continue
            u=node(node(node(0,1),middle),node(5,6))
            k,forests=optimum_refinement(t,u,blocks)
            instance_count+=1
            if not any(any((avoids(t,p,blocks[1],e) and avoids(t,p,blocks[1],f))
                           or (avoids(t,p,blocks[0],e) and avoids(t,p,blocks[2],f))
                           for p in forests) for e,f in product(ea,ec)):
                witness={'T':t,'Tprime':u,'blocks':[sorted(z) for z in blocks],
                         'AB_edges':list(ea),'BC_edges':list(ec),
                         'optimum_components':k,'optimal_forests':forests,
                         'scope':'Synthetic tree-forest state; baseline reachability unproved.'}
                break
        if witness:
            break
    result={'trees_checked':total,'path_trees':path_count,'instances_checked':instance_count,
            'counterexample':witness,'elapsed_seconds':time.monotonic()-start,
            'complete':total==len(trees(tuple(range(7)))) and not args.limit,
            'scope':'Synthetic path-overlap states, not necessarily reachable baseline children.'}
    suffix='pilot' if args.limit else 'full'
    path=Path(__file__).parents[1]/'results'/f'branching-synthetic-exchange-{suffix}.json'
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='counterexample'},indent=2))
    print('exchange refuted',bool(witness))


if __name__=='__main__':
    main()
