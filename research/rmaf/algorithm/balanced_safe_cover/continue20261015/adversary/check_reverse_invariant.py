#!/usr/bin/env python3
"""One-shot source/formula invariant tests, post-pilot pin INVARIANT-PIN-v1.md."""
import itertools,time,json
from pathlib import Path
import independent_cb1 as X

def cat(L):return L[0] if len(L)==1 else [L[0],cat(L[1:])]
def p(i,N):return 2*i-2 if i<N else 2*N-3
def g(i):return 2*i-1

def formula_full(N):
    return X.minimal(tuple(sum(1<<p(i,N) for i in A)|sum(1<<g(i) for i in range(A[0],min(A[-1],N-1))) for A in itertools.combinations(range(1,N+1),3)))

def columns(H):
    U=0
    for h in H:U|=h
    return {e:sum(1<<i for i,h in enumerate(H) if h>>e&1) for e in range(U.bit_length()) if U>>e&1}

def maximal_columns(H):
    C=columns(H);return {e for e,I in C.items() if not any(I!=J and I&J==I for J in C.values())}

def formula_projected(N):
    if N<5:return X.quotient(formula_full(N))
    U=sum(1<<g(i) for i in range(2,N-1))|sum(1<<p(i,N) for i in range(3,N-1))
    return X.minimal(tuple(h&U for h in formula_full(N)))

def remap_rows(H,mapping):
    return X.minimal(tuple(sum(1<<mapping[e] for e in range(h.bit_length()) if h>>e&1) for h in H))

def verify_transition(N,kind):
    K=formula_projected(N);e=g(2) if kind=='gap' else p(3,N)
    R=X.quotient(tuple(h for h in K if not h>>e&1));M=N-(2 if kind=='gap' else 1)
    if M<5:
        assert len(R)==1 and R[0].bit_count()==1
        return
    if kind=='gap':
        mapping={g(i):g(i-2) for i in range(4,N-1)}|{p(i,N):p(i-2,M) for i in range(5,N-1)}
    else:
        mapping={g(2):g(2)}|{g(i):g(i-1) for i in range(4,N-1)}|{p(i,N):p(i-1,M) for i in range(4,N-1)}
    assert remap_rows(R,mapping)==formula_projected(M),(N,kind,R,mapping)

out=[];start=time.perf_counter()
for N in range(3,14):
    t=time.perf_counter();L=[str(i) for i in range(1,N+1)];S,T=X.Tree(cat(L)),X.Tree(cat(L[::-1]));H=X.conflicts(S,T);F=formula_full(N)
    assert H==F,(N,'tree/formula');assert len(X.factors(H))==1
    R=X.quotient(H);assert R==formula_projected(N)
    if N>=5:
        actual=maximal_columns(H);expected={g(i) for i in range(2,N-1)}|{p(i,N) for i in range(3,N-1)};assert actual==expected
        pairs={h for h in R if h.bit_count()==2};expectpairs={(1<<g(2))|(1<<p(3,N)),(1<<p(N-2,N))|(1<<g(N-2))}
        if N==5:expectpairs.add((1<<g(2))|(1<<g(3)))
        assert pairs==expectpairs and min(h.bit_count() for h in R)==2
        assert min(R,key=lambda h:(h.bit_count(),h))==(1<<g(2))|(1<<p(3,N))
        verify_transition(N,'gap');verify_transition(N,'pendant')
        assert actual != expected-{g(2)} # deliberate omission must fail equality
        assert pairs != expectpairs-{(1<<g(2))|(1<<p(3,N))}
    rec={'N':N,'raw_rows':len(H),'quotient_rows':len(R),'factors':len(X.factors(H)),'seconds':time.perf_counter()-t}
    if N%2==1 and N>=5:
        b=(N-1)//2;s={'nodes':0,'max_rank':0,'rank_counts':{}};w=X.search(H,b-1,s);assert w is None and s['nodes']==2**b-1 and s['rank_counts']=={'2':2**(b-1)-1};rec['failed_trial']={'budget':b-1,**s}
    out.append(rec)
    assert rec['seconds']<10
assert X.solve([],0)['cuts']==0 and X.solve([1],1)['cost']==1
result={'status':'FINITE_INVARIANT_TESTS_PASS','scope':'N3..13 and failed odd-N budgets b-1 for b2..6; post-pilot development checks','cases':out,'seconds':time.perf_counter()-start,'negative_formula_controls':18}
Path('results/algorithm-balanced-cover-continue-adversary-reverse-invariant-v1.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'cases':len(out),'seconds':result['seconds'],'failed_trial_nodes':[r['failed_trial']['nodes'] for r in out if 'failed_trial' in r]}))
