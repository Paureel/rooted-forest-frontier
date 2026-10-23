#!/usr/bin/env python3
"""One-shot Q-HALF-ANY falsification, production-side development.
Shares own quotient_probe exact source enumeration; NOT independent review.
"""
import json,itertools,time,hashlib
from pathlib import Path
from quotient_probe import Tree,tup,restrict,agreement,optima,ROOT

def pure(T,blocks):
    H=[T.support(B) for B in blocks];rows=[]
    def degree(H,v):
        return sum((a==v and b in H) or (b==v and a in H) for a,b in T.edges)
    for i,j in itertools.combinations(range(len(H)),2):
        for v in sorted(H[i]&H[j]):
            rows.append({'components':[i,j],'vertex':v,'degrees':[degree(H[i],v),degree(H[j],v)]})
    return all(x['degrees']==[2,2] for x in rows),rows

def leaves_below(T,v):
    out=set()
    todo=[v]
    while todo:
        w=todo.pop()
        if w in T.label:out.add(T.label[w])
        todo.extend(T.ch[w])
    return out

def check(S,T,C,b):
    F=S.certificate(C);blocks=[L for L,_ in F]
    isp,rows=pure(T,blocks)
    ds=[]
    for L in blocks:
        d,_,_=optima(Tree(restrict(S.t,L)),Tree(restrict(T.t,L)))
        ds.append({'labels':sorted(L),'d':d,'matches':restrict(S.t,L)==restrict(T.t,L)})
    terminal=all(x['matches'] or len(x['labels'])==3 for x in ds)
    return {'cuts':C,'blocks':[sorted(B) for B in blocks],'pure':isp,'overlap_degrees':rows,'compatible_or_triple':terminal,'local':ds,'tau':max(x['d'] for x in ds),'half_budget':all(x['d']<=b//2 for x in ds)}

def main():
    pin=Path(__file__).with_name('GEOMETRY-CONTROLS-v1.json'); controls=json.loads(pin.read_text())
    passed=[]
    for kind in ('positive','corruption'):
        f=controls[kind];actual,_=pure(Tree(tup(f['target'])),[set(B) for B in f['blocks']])
        assert actual==f['pure'];passed.append({'id':kind,'expected_pure':f['pure'],'actual_pure':actual,'passed':True})
    S=Tree(tup([[['c',['a','b']],'d'],[['e','f'],'g']]))
    T=Tree(tup([['a',[[['e',['c','d']],'f'],'g']],'b']))
    tic=time.perf_counter();b,fs,n=optima(S,T);seconds=time.perf_counter()-tic
    K=tuple(e for e in S.edges if leaves_below(S,e[1]) in ({'a','b'},{'e','f','g'}))
    F=S.certificate(K)
    Kopt=len(K)==b and agreement(S,T,[L for L,_ in F])
    rows=[check(S,T,C,b) for C in itertools.combinations(K,(b+1)//2)] if Kopt else []
    result={'kind':'GLOBAL-Q geometry development witness; not existential-cover refutation','controls':passed,'source':S.t,'target':T.t,'opt':b,'examined_source_cut_sets':n,'optimal_realization_count':len(fs),'pilot_seconds':seconds,'K':K,'K_blocks':[sorted(L) for L,_ in F],'K_is_original_optimum':Kopt,'half_subset_rows':rows,'Q_HALF_ANY_refuted':any(not(row['pure'] or row['compatible_or_triple']) for row in rows),'existential_some_half_subset_terminal':any(row['pure'] or row['compatible_or_triple'] for row in rows),'lineage':'own prior finite development oracle; no independent certification','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    out=ROOT/'results/algorithm-balanced-cover-quotient-geometry.json';out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('opt','K_is_original_optimum','Q_HALF_ANY_refuted','existential_some_half_subset_terminal','pilot_seconds')}))
if __name__=='__main__':main()
