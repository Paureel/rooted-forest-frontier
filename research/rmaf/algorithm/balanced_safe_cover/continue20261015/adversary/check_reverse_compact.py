#!/usr/bin/env python3
"""One-shot compact K_N formula check; post-pilot proof-development evidence."""
import itertools,json,time
from pathlib import Path
import independent_cb1 as X

def g(i):return 2*i-1
def p(i):return 2*i-2
def mask(E):return sum(1<<e for e in E)
def compact(N):
    I=range(3,N-1)
    rows=[mask([p(i)]+[g(j) for j in range(2,i)]) for i in I]
    rows +=[mask([p(i)]+[g(j) for j in range(i,N-1)]) for i in I]
    rows +=[mask([g(j) for j in range(2,N-1)])]
    rows +=[mask([p(a),p(b),p(c)]+[g(j) for j in range(a,c)]) for a,b,c in itertools.combinations(I,3)]
    return tuple(sorted(rows))

def full(N):
    def pp(i):return p(i) if i<N else 2*N-3
    return X.minimal(tuple(mask([pp(a),pp(b),pp(c)]+[g(j) for j in range(a,min(c,N-1))]) for a,b,c in itertools.combinations(range(1,N+1),3)))

A=[];start=time.perf_counter()
for N in range(5,21):
    t=time.perf_counter();K=compact(N)
    assert K==X.quotient(full(N))
    assert K==X.minimal(K)==X.quotient(K)
    assert len(K)==2*(N-4)+1+len(list(itertools.combinations(range(N-4),3)))
    for h in K:
        assert h.bit_count()>=2
    pairs={h for h in K if h.bit_count()==2}
    expected={mask([g(2),p(3)]),mask([p(N-2),g(N-2)])}
    if N==5:expected.add(mask([g(2),g(3)]))
    assert pairs==expected
    A.append({'N':N,'rows':len(K),'idempotent_quotient':True,'seconds':time.perf_counter()-t})
assert compact(7)!=compact(7)[:-1]
result={'status':'COMPACT_FORMULA_PASS','cases':A,'seconds':time.perf_counter()-start,'negative_omitted_row_caught':True,'scope':'post-pilot proof-development; no held-out certification'}
Path('results/algorithm-balanced-cover-continue-adversary-reverse-compact-v1.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['status','seconds','negative_omitted_row_caught']}))
