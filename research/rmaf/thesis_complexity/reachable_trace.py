#!/usr/bin/env python3
"""One-shot exact structural replay of three thesis branches, not a full MAF solver.
No other arm code is imported. Standard-library immutable labelled rooted trees.
"""
from dataclasses import dataclass, replace
from pathlib import Path
import hashlib,json,time
ROOT=Path(__file__).resolve().parents[1]; HERE=Path(__file__).resolve().parent
@dataclass(frozen=True)
class N:
    name: str|None=None
    kids: tuple=()
    protected: bool=False

def leaf(x):return N(x)
def pair(x,y):return N(kids=(x,y))
def rho(x):return N('rho',(x,))
def shape(t):return t.name if not t.kids else (t.name,tuple(shape(c) for c in t.kids))
def labels(t):return frozenset(([t.name] if t.name else [])).union(*(labels(c) for c in t.kids))
def key(t):return ','.join(sorted(labels(t)))
def newick(t):return t.name if not t.kids else '('+','.join(newick(c) for c in t.kids)+')'+(t.name or '')
def maps(t):
    ns={};ps={};ds={}
    def go(n,p,d):
        k=key(n);ns[k]=n;ps[k]=p;ds[k]=d
        for c in n.kids:go(c,k,d+1)
    go(t,None,0)
    return ns,ps,ds

def mark(t,ks):return replace(t,protected=t.protected or key(t) in ks,kids=tuple(mark(c,ks) for c in t.kids))
def cut(t,k):
    if key(t)==k:return None
    children=tuple(x for c in t.kids if (x:=cut(c,k)) is not None)
    if not t.kids:return t
    if not children:return t if t.name else None
    if len(children)==1 and not t.name:return replace(children[0],protected=children[0].protected or t.protected)
    return replace(t,kids=children)
def protected(t):return sorted(k for k,v in maps(t)[0].items() if v.protected)
def sibling(k,ns,ps):
    p=ps[k]
    if p is None:return None
    return next((key(c) for c in ns[p].kids if key(c)!=k),None)
def legal(t,ks):
    ns,ps,_=maps(t)
    for k in ks:
        if ns[k].protected:return False
        p=ps[k];s=sibling(k,ns,ps)
        if p is not None and ps[p] is None and s and ns[s].protected:return False
    return True

def path_data(t,a,c):
    ns,ps,ds=maps(t);aa=[];cc=[]
    z=a
    while z is not None:aa.append(z);z=ps[z]
    z=c
    while z is not None:cc.append(z);z=ps[z]
    lca=next(z for z in aa if z in cc)
    path=aa[:aa.index(lca)+1]+list(reversed(cc[:cc.index(lca)]))
    pend=[key(ch) for z in path[1:-1] for ch in ns[z].kids if key(ch) not in path]
    return lca,path,pend

def eligible_pairs(f1,f2):
    ns,ps,ds=maps(f1); ns2,ps2,ds2=maps(f2)
    candidates=[tuple(key(c) for c in v.kids) for v in ns.values() if len(v.kids)==2 and all(not c.kids for c in v.kids)]
    tops=[ps[k] for k in protected(f1)]
    top=max(tops,key=lambda k:ds[k]) if tops else key(f1)
    elig=[ab for ab in candidates if all(labels(ns[x])<=labels(ns[top]) for x in ab)]
    def rank(ab):return (ds[ab[0]],max(ds2[x] for x in ab))
    best=max(rank(ab) for ab in elig)
    return [ab for ab in elig if rank(ab)==best], {'deepest_protected_top':top,'eligible':elig,'all_candidates':candidates,'best_rank':best}

def classify(f1,f2,ab):
    ns,ps,ds=maps(f1);ns2,ps2,ds2=maps(f2)
    a,c=sorted(ab,key=lambda x:(-ds2[x],x))
    x=sibling(ps[a],ns,ps); x2=next((k for k,n in ns2.items() if x and shape(n)==shape(ns[x])),None)
    lca,path,pend=path_data(f2,a,c);q=len(pend)
    sa=sibling(a,ns2,ps2);sc=sibling(c,ns2,ps2)
    rb=(x is not None and ((sa and shape(ns2[sa])==shape(ns[x])) or (sc and shape(ns2[sc])==shape(ns[x]))))
    chain=ns2[pend[0]] if pend else None
    if q>=2:
        chain=pair(ns2[pend[0]],ns2[pend[1]])
        for b in pend[2:]:chain=pair(chain,ns2[b])
    rbs=q>=2 and ps2[c]==lca and x is not None and shape(ns[x])==shape(chain)
    sl=sibling(lca,ns2,ps2)
    twob=q==2 and x is not None and sl is not None and shape(ns[x])==shape(ns2[sl])
    bcy=q>=2 and x2 is not None and ns2[x2].protected and ps2[x2]==pend[0]
    if ps2[a]==ps2[c]:case='merge'
    elif q==1:case='B'
    elif rb:case='RB'
    elif rbs:case='RB*'
    elif twob:case='2B'
    elif bcy:case='BCY'
    elif q==2:case='A2BC'
    else:case='A3BC'
    branches=[]
    if case=='A2BC':
        if not ns2[c].protected:
            branches=[('A',[a],[],[]),('B',pend,[],[]),('C',[c],[a]+pend,[a])]
        else:branches=[('B',pend,[],[]),('A',[a],pend,[])]
    elif case=='A3BC':branches=[('A',[a],[],[]),('B',pend,[],[]),('C',[c],[a],[a])]
    return {'pair':[a,c],'case':case,'uncle':x,'lca':lca,'pendants':pend,'predicates':{'RB':bool(rb),'RB*':bool(rbs),'2B':bool(twob),'BCY':bool(bcy)},
            'branches':[{'name':b,'cuts':cs,'protect2':p2,'protect1':p1,'legal':legal(f2,cs)} for b,cs,p2,p1 in branches]}

def main():
    start=time.monotonic(); raw=(HERE/'trace-controls-frozen.json').read_bytes();json.loads(raw)
    t=rho(pair(pair(leaf('a'),leaf('b')),leaf('c')))
    v=mark(t,['a,b']);v2=cut(v,'b')
    assert newick(v2)=='((a,c))rho' and protected(v2)==['a']
    assert not legal(mark(t,['b']),['b'])
    assert cut(t,'ABSENT')==t
    # Frozen synthetic restriction control.
    f1=rho(pair(pair(leaf('a'),leaf('d')),pair(leaf('x'),leaf('y'))))
    f2=rho(pair(pair(leaf('a'),leaf('d')),pair(leaf('x'),leaf('y'))))
    ep,_=eligible_pairs(mark(f1,['a']),f2)
    assert ('a','d') in ep and ('x','y') not in ep
    controls={'count':4,'passed':4,'state_corruption_caught':True,'sha256':hashlib.sha256(raw).hexdigest()}
    L=leaf
    f1=rho(pair(pair(pair(pair(L('a'),L('c')),L('d')),pair(L('x'),L('y'))),pair(pair(L('z'),L('w')),pair(L('t'),L('h')))))
    b1=pair(pair(L('x'),L('z')),pair(L('d'),pair(pair(L('y'),L('w')),L('t'))))
    f2=rho(pair(pair(pair(L('a'),b1),L('h')),L('c')))
    trace=[]
    for pair_expected,case_expected,cut_leaf,credit in [(('a','c'),'A2BC','c',[0,0]),(('a','d'),'A2BC','d',[1,0]),(('x','y'),'A3BC',None,[1,0])]:
        pairs,selection=eligible_pairs(f1,f2)
        assert any(set(p)==set(pair_expected) for p in pairs),(pairs,pair_expected)
        info=classify(f1,f2,pair_expected)
        assert info['case']==case_expected,info
        row={'F1':newick(f1),'F2':newick(f2),'protected_F1':protected(f1),'protected_F2':protected(f2),
             'P_Q_cardinalities':credit,'selection':selection,**info}
        trace.append(row)
        if cut_leaf:
            branch=next(b for b in info['branches'] if b['cuts']==[cut_leaf]);assert branch['legal']
            row['chosen_branch']=branch['name']
            f2=cut(mark(f2,branch['protect2']),cut_leaf)
            f1=cut(mark(f1,branch['protect1']),cut_leaf)
        else:
            assert len(info['branches'])==3 and all(b['legal'] for b in info['branches'])
    out={'scope':'exact three-branch structural trace, all labels including unary rho retained; not total runtime counterexample',
         'controls':controls,'leaf_count_excluding_rho':9,'trace':trace,'elapsed_seconds':time.monotonic()-start,
         'finding':'G4.1 A3BC with incoming P={a},Q=empty is reachable by two A2BC cuts; local credit substitution overshoots'}
    (ROOT/'results/thesis-complexity-reachable-trace.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'controls_passed':4,'cases':[r['case'] for r in trace],'last_legal_branches':3,'elapsed_seconds':out['elapsed_seconds']}))
if __name__=='__main__':main()
