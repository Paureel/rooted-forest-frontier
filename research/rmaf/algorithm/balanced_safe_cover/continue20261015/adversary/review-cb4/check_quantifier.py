#!/usr/bin/env python3
"""Replay the two actual CB4 states refuting an all-reachable-states optimum claim."""
import sys,json
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import review_cb4 as R
F=json.loads((R.BASE.parent/'CONTROLS-frozen-v1.json').read_text())['ordinary']
f=next(f for f in F if f['id']=='quotient-star');M=R.Model(f['source'],f['target'],3);out=[]
for mask in (65,257):
    C={M.SE[e] for e in range(mask.bit_length()) if mask>>e&1};parts=R.graph_parts(M.S,M.S.adj,C);best=99;wins=[]
    for P in R.X.partitions(M.S.labels):
        if all(any(B<=L for L,V in parts) for B in P) and R.X.agreement(M.S,M.T,P):
            cost=max(0,len(P)-1)
            if cost<best:best=cost;wins=[]
            if cost==best:wins.append([sorted(B) for B in P])
    assert best==4
    out.append({'prefix_mask':mask,'original_source_edge_indices':[e for e in range(mask.bit_length()) if mask>>e&1],'precut_partition':[sorted(L) for L,V in parts],'original_optimum':3,'minimum_total_cuts_refining_prefix':best,'refining_optimum_partition':wins[0]})
print(json.dumps({'status':'QUANTIFIER_WITNESSES_REPRODUCED','states':out}))
