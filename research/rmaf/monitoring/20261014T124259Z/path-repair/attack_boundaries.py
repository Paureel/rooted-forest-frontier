#!/usr/bin/env python3
"""Targeted in/out-of-regime boundary attacks using the discovery instrument.
Expected failures pinned in the journal before execution. Not fresh certification.
"""
import hashlib, json, time
from pathlib import Path
from check_geometry import Tree, local_candidates, opt, eliminate, brute_completion, assert_equal
start=time.monotonic()
# Removing a degree-three internal vertex creates three leaf regions.
t=Tree(((0,1),2)); internal=t.child[0][0]
h=opt(local_candidates(t,t),{internal})['cost']
assert_equal(t.degree(internal,t.span(t.labels)),3);assert_equal(h,2)
# Deepest pair's root has degree three in its neighbor: greedy marking costs 2.
t=Tree(((0,1),((2,3),(4,5)))); sources=[Tree((2,4)),Tree(((0,1),(3,5)))]
assert eliminate(t,sources) is None
unsafe=eliminate(t,sources,require_pure=False); exact=brute_completion(t,sources)
assert_equal(unsafe[0],2);assert_equal(exact[0],1)
# Arbitrarily high-degree clique, with explicit expected optimum m-1.
def comb(xs):
    if len(xs)==1:return xs[0]
    return (xs[0],comb(xs[1:]))
cliques=[]
for m in [2,3,4,6,10]:
    target=Tree((comb(list(range(m))),comb(list(range(m,2*m)))))
    src=[Tree((i,i+m)) for i in range(m)]
    val,steps=eliminate(target,src); direct=brute_completion(target,src)[0]
    assert_equal(val,m-1);assert_equal(direct,m-1)
    cliques.append({'m':m,'optimum':val,'largest_elimination_neighborhood':max(x['neighbors'] for x in steps)})
report={'status':'tested','degree_three_one_cut_counterexample':{'tree':((0,1),2),'marked_vertex':internal,'degree':3,'unmarked_cost':0,'marked_cost':h},'nonpure_elimination_counterexample':{'target':t.syntax,'sources':[s.syntax for s in sources],'greedy_cost':unsafe[0],'exact_cost':exact[0],'greedy_steps':unsafe[1],'exact_blocks':[c['blocks'] for c in exact[1]]},'cliques':cliques,'seconds':time.monotonic()-start,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256((Path(__file__).parent/'check_geometry.py').read_bytes()).hexdigest()}
dest=Path(__file__).resolve().parents[3]/'results/pure-bridge-boundaries.json';dest.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
