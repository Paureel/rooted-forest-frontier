"""Supplementary finite B2 check of all labelled trees through four leaves.
Independent root bipartition generator, no original shape-quotient argument.
"""
import itertools,json,time
from functools import lru_cache
from pathlib import Path
from independent_graph import exact
from review_paid import frontier
HERE=Path(__file__).resolve().parent; OUT=HERE.parents[1]/'results'
@lru_cache(None)
def trees(labels):
    if not labels: return (None,)
    if len(labels)==1: return (labels[0],)
    head,*rest=labels; out=[]
    for r in range(len(rest)):
        for chosen in itertools.combinations(rest,r):
            left=tuple([head,*chosen]); right=tuple(x for x in labels if x not in left)
            for a,b in itertools.product(trees(left),trees(right)): out.append((a,b))
    return tuple(out)
def score(a,b):
    opt=exact(a,b)
    if a is None:return {'q':0,'retained_total':0,'survives':True}
    f=frontier(a,b,opt['cuts'],first=True)
    totals=[exact(a,b,required_refinement=s['partition'])['cuts'] for s in f['states']]
    assert totals
    return {'q':opt['cuts'],'retained_total':min(totals),'survives':min(totals)==opt['cuts']}
before=time.perf_counter(); pilot=score(((0,1),(2,3)),((0,2),(1,3))); elapsed=time.perf_counter()-before
(OUT/'algorithm-review-B2-smallness-pilot.json').write_text(json.dumps({'one_cross_quartet_seconds':elapsed,'projection_237_pairs_seconds':237*elapsed,'assumption':'constant small n<=4 per-pair upper proxy; supplementary finite task'},indent=2)+'\n')
rows=[]; before=time.perf_counter()
for n,expected in enumerate([1,1,1,3,15]):
    ts=trees(tuple(range(n))); assert len(ts)==expected
    cases=[]
    for a,b in itertools.product(ts,repeat=2):
        s=score(a,b); assert s['survives'],(a,b,s);cases.append(s)
    rows.append({'n':n,'tree_count':len(ts),'pair_count':len(cases),'all_survive':True,'rows':cases})
count=sum(r['pair_count'] for r in rows); assert count==237
(OUT/'algorithm-review-B2-smallness-through4.json').write_text(json.dumps({'scope':'supplementary independent finite labelled universe through4, no source quotient reused; no universal statement','pairs':count,'rows':rows,'seconds':time.perf_counter()-before},indent=2)+'\n')
print(json.dumps({'pairs':count,'all_B2_survive':True,'seconds':time.perf_counter()-before}))
