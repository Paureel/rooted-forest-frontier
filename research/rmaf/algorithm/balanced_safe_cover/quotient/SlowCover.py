#!/usr/bin/env python3
"""Total original-edge exhaustive safe cover with explicitly unlicensed cost.
Problem-specific fallback, not an improved FPT algorithm. No optimum oracle,
no completion optimizer, and no implicit root label are used. Tree primitives
come from our production-side development instrument; no independence claim.
"""
import itertools
from quotient_probe import Tree,tup,restrict,agreement

def validate_input(s,t,b):
    if not isinstance(b,int) or isinstance(b,bool) or b<0:
        raise ValueError('budget must be a nonnegative integer')
    def check(x,seen):
        if isinstance(x,str):
            if x in seen:raise ValueError('duplicate original leaf label')
            seen.add(x);return x
        if not isinstance(x,(list,tuple)) or len(x)!=2:
            raise ValueError('ordinary nonempty rooted binary syntax required')
        return (check(x[0],seen),check(x[1],seen))
    A=set();B=set();s=check(s,A);t=check(t,B)
    if A!=B:raise ValueError('source and target labels differ')
    return Tree(s),Tree(t)

def generate_slow(s,t,b):
    """Yield every original-edge agreement certificate within the budget.
    This is a cover of already completed, hence all-compatible, forests.
    Time and candidate count: poly(n) * sum_{i<=min(b,n-1)} C(2n-2,i).
    """
    S,T=validate_input(s,t,b)
    for r in range(min(b,len(S.labels)-1)+1):
        for C in itertools.combinations(S.edges,r):
            F=S.certificate(C)
            if F is None or not agreement(S,T,[L for L,_ in F]):continue
            yield {'original_source_edges':[list(e) for e in C],
                   'precut_cost':r,'residual_cost':0,'total_cost':r,
                   'components':[{'original_labels':sorted(L),
                                  'full_original_vertices':sorted(V),
                                  'source_restriction':restrict(S.t,L),
                                  'target_support':sorted(T.support(L))}
                                 for L,V in F]}

def verify_certificate(s,t,b,cert):
    S,T=validate_input(s,t,b)
    cuts=[tuple(e) for e in cert['original_source_edges']]
    if len(cuts)!=len(set(cuts)) or len(cuts)>b:return False
    F=S.certificate(cuts)
    if F is None or not agreement(S,T,[L for L,_ in F]):return False
    r=len(cuts)
    if (cert['precut_cost'],cert['residual_cost'],cert['total_cost'])!=(r,0,r):return False
    expected=[{'original_labels':sorted(L),'full_original_vertices':sorted(V),
               'source_restriction':restrict(S.t,L),'target_support':sorted(T.support(L))}
              for L,V in F]
    return cert['components']==expected and len(expected)==r+1

def decide_slow(s,t,b):
    answer=None
    for cert in generate_slow(s,t,b):
        if answer is None or cert['total_cost']<answer['total_cost']:answer=cert
    return answer

def optimize_slow(s,t):
    S,_=validate_input(s,t,0)
    for b in range(len(S.labels)):
        answer=decide_slow(s,t,b)
        if answer is not None:return answer
    raise AssertionError('all singleton original cut certificate must exist')
