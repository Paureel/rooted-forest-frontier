#!/usr/bin/env python3
"""Bounded small-tree census for minimal quotient witness size.
Uses our own development oracle; cannot independently certify it.
"""
from functools import lru_cache
import itertools,json,time,sys
from quotient_probe import Tree,optima,canon,ROOT
@lru_cache(None)
def trees(labels):
    if len(labels)==1:return (labels[0],)
    out=[];a=labels[0];rest=labels[1:]
    for k in range(len(rest)):
        for selected in itertools.combinations(rest,k):
            L=(a,)+selected;R=tuple(x for x in rest if x not in selected)
            if not R:continue
            for x in trees(L):
                for y in trees(R):out.append(canon((x,y)))
    assert len(out)==len(set(out))
    return tuple(out)
def census(n):
    ts=trees(tuple('abcde'[:n]));assert len(ts)=={1:1,2:1,3:3,4:15,5:105}[n]
    begin=time.perf_counter();counts={};examined=0;first=None
    for s,t in itertools.product(ts,repeat=2):
        b,_,cost=optima(Tree(s),Tree(t));examined+=1
        counts[b]=counts.get(b,0)+1
        if b>=3:first={'source':s,'target':t,'opt':b};break
    return {'n':n,'tree_count':len(ts),'pairs_examined':examined,'complete':examined==len(ts)**2,'optimum_counts':counts,'first_three_cut_pair':first,'seconds':time.perf_counter()-begin}
mode=sys.argv[1]
if mode=='pilot':rows=[census(n) for n in (1,2,3,4)]
else:rows=[census(5)]
out=ROOT/f'results/algorithm-balanced-cover-quotient-smallest-{mode}.json'
out.write_text(json.dumps({'scope':'same-author finite minimal-size search, not independent verification','rows':rows},indent=2)+'\n')
print(json.dumps({'mode':mode,'rows':rows}))
