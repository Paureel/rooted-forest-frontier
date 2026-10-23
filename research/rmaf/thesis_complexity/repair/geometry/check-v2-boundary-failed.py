#!/usr/bin/env python3
"""One-shot source-rule geometry checker; no imported problem evaluator.
Run controls first, then seeded bounded geometry search; exact rational boundary mass.
Boundary is reached when a is no longer active, not a claim of source credit resets.
"""
from __future__ import annotations
import argparse, copy, hashlib, json, random, re, time
from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path

@dataclass
class N:
    kids:list[N]=field(default_factory=list)
    atoms:frozenset[str]=frozenset()
    p:bool=False
    rho:bool=False
    def key(self):
        return frozenset().union(*(x.key() for x in self.kids)) if self.kids else self.atoms
    def text(self):
        return ('('+','.join(x.text() for x in self.kids)+')'+('rho' if self.rho else '')) if self.kids else '+'.join(sorted(self.atoms))

def parse(s):
    ts=re.findall(r'[(),]|[^(),\s]+',s); i=0
    def rec():
        nonlocal i
        if ts[i]!='(':
            v=N(atoms=frozenset([ts[i]]));i+=1;return v
        i+=1; kids=[rec()]
        while ts[i]==',':i+=1;kids.append(rec())
        assert ts[i]==')';i+=1
        rho=i<len(ts) and ts[i]=='rho'
        if rho:i+=1
        if len(kids)==1 and not rho:return kids[0]
        return N(kids=kids,rho=rho)
    t=rec();assert i==len(ts),(i,ts)
    return t if t.rho else N(kids=[t],rho=True)

def ix(fs):
    nodes={};parents={};depth={};comp={}
    def walk(n,pa,d,c):
        # rho and its child have same leaf cluster; keep rho separate.
        key=frozenset({'rho'})|n.key() if n.rho else n.key()
        nodes[key]=n;parents[key]=pa;depth[key]=d;comp[key]=c
        for ch in n.kids:walk(ch,key,d+1,c)
    for c,t in enumerate(fs):walk(t,None,0,c)
    return nodes,parents,depth,comp

def label(s):return frozenset(s.split(','))
def protected(fs):return sorted(','.join(sorted(k)) for k,n in ix(fs)[0].items() if n.p)
def mark(fs,keys):
    ns=ix(fs)[0]
    for k in keys:ns[k].p=True

def simplify(n):
    if n.rho:return n
    if len(n.kids)==1:
        c=n.kids[0];c.p |= n.p;return c
    return n

def cut(fs,keys):
    keys=set(keys);out=[]
    def rec(n):
        if not n.rho and n.key() in keys:
            n.p=False;out.append(n);return None
        if not n.kids:return n
        n.kids=[z for c in n.kids if (z:=rec(c)) is not None]
        if not n.kids:return n if n.rho else None
        return simplify(n)
    remain=[]
    for t in fs:
        z=rec(t)
        if z is not None:remain.append(z)
    return remain+out

def prune(t,key):
    if not t.rho and t.key()==key:return None
    if not t.kids:return t
    t.kids=[z for c in t.kids if (z:=prune(c,key)) is not None]
    if not t.kids:return t if t.rho else None
    return simplify(t)

def contract(fs,key):
    n=ix(fs)[0][key];n.atoms=key;n.kids=[]

def pairdata(fs,a,c):
    ns,pa,ds,co=ix(fs)
    if co[a]!=co[c]:return [],None
    aa=[];q=a
    while q is not None:aa.append(q);q=pa[q]
    cc=[];q=c
    while q not in aa:cc.append(q);q=pa[q]
    r=q;path=aa[:aa.index(r)+1]+list(reversed(cc));pend=[]
    for j,k in enumerate(path[1:-1],1):
        for ch in ns[k].kids:
            ck=ch.key()
            if ck not in (path[j-1],path[j+1]):pend.append(ck)
    return pend,r

def sibling(ns,pa,k):
    if pa[k] is None:return None
    z=[ch.key() for ch in ns[pa[k]].kids if ch.key()!=k]
    return z[0] if z else None

def cherries(t):
    out=[]
    def rec(n):
        if len(n.kids)==2 and all(not x.kids for x in n.kids):out.append(tuple(x.key() for x in n.kids))
        for x in n.kids:rec(x)
    rec(t);return out

def selection(f1,f2):
    n1,p1,d1,_=ix([f1]);n2,p2,d2,c2=ix(f2)
    tops=[p1[k] for k,n in n1.items() if n.p and p1[k] is not None]
    top=max(tops,key=lambda k:d1[k]) if tops else None
    pairs=[p for p in cherries(f1) if top is None or all(k<=top for k in p)]
    def rank(p):
        a,c=p;return d1[a],int(c2[a]!=c2[c]),max(d2[a],d2[c])
    best=max(map(rank,pairs)) if pairs else None
    return [p for p in pairs if rank(p)==best]

def legal(fs,keys):
    ns,pa,_,_=ix(fs)
    for k in keys:
        if pa[k] is None or ns[k].p:return False
        sk=sibling(ns,pa,k)
        if pa[pa[k]] is None and sk is not None and ns[sk].p:return False
    return True

def rules(f1,f2,a,c):
    ns,pa,d,co=ix(f2);n1,p1,_,_=ix([f1]);pp=p1[a]
    uncle=sibling(n1,p1,pp) if p1[pp] is not None else None
    pend,r=pairdata(f2,a,c);s=len(pend)
    def br(name,ks,p2=(),p1=()):return dict(name=name,cuts=list(ks),protect2=list(p2),protect1=list(p1),legal=legal(f2,ks))
    if co[a]!=co[c]:case='AC';bs=[br('A',[a]),br('C',[c])]
    elif s==1:case='B';bs=[br('B',pend)]
    elif uncle is not None and sibling(ns,pa,a)==uncle:case='RB';bs=[br('C',[c])]
    elif uncle is not None and sibling(ns,pa,c)==uncle:case='RB';bs=[br('A',[a])]
    else:
        chain=None
        if s>=2:
            chain=pend[0]|pend[1]
            good=all(k in n1 and not n1[k].kids for k in pend)
            good=good and chain in n1 and {z.key() for z in n1[chain].kids}=={pend[0],pend[1]}
            for k in pend[2:]:
                new=chain|k;good=good and new in n1 and {z.key() for z in n1[new].kids}=={chain,k};chain=new
            good=good and chain==uncle and pa[c]==r
        else:good=False
        if good:case='RB*';bs=[br('A',[a])]
        elif s==2 and uncle in ns and sibling(ns,pa,r)==uncle:case='2B';bs=[br('B',pend)]
        elif s>=2 and uncle in ns and ns[uncle].p and pa[uncle]==pend[0]:
            case='BCY';bs=[br('B',pend),br('CY',[c,sibling(ns,pa,uncle)])]
        elif s==2:
            case='A2BC'
            bs=[br('B',pend),br('A',[a],pend)] if ns[c].p else [br('A',[a]),br('B',pend),br('C',[c],[a]+pend,[a])]
        elif s>=3:case='A3BC';bs=[br('A',[a]),br('B',pend),br('C',[c],[a],[a])]
        else:raise AssertionError(('trivial',a,c,s))
    return dict(pair=(a,c),case=case,pendants=pend,branches=bs,uncle=uncle)

def normal(f1,f2,chosen=None):
    while True:
        if len([n for n in ix([f1])[0].values() if not n.kids])+1<=2:return None
        choices=selection(f1,f2)
        pair=next((p for p in choices if set(p)==set(chosen)),None) if chosen else choices[0]
        requested = pair is not None and chosen is not None
        pair = pair or choices[0]
        a,c=pair;ns,pa,d,_=ix(f2)
        if requested:
            a,c=chosen;assert d[a]>=d[c],('wrong orientation',d[a],d[c])
        elif d[c]>d[a]:a,c=c,a
        if pa[a]==pa[c] and pa[a] is not None:
            key=a|c;contract([f1],key);contract(f2,key)
        elif pa[a] is None:
            f1=prune(f1,a);f2=[t for t in f2 if t.key()!=a]
        elif pa[c] is None:
            f1=prune(f1,c);f2=[t for t in f2 if t.key()!=c]
        else:
            assert chosen is None or requested,('bad depth pair',chosen,choices)
            return f1,f2,rules(f1,f2,a,c)

def child(f1,f2,b):
    assert b['legal'];f1=copy.deepcopy(f1);f2=copy.deepcopy(f2)
    mark([f1],b['protect1']);mark(f2,b['protect2']);f2=cut(f2,b['cuts'])
    return f1,f2

def freeze(v):
    if isinstance(v,frozenset):return ','.join(sorted(v))
    if isinstance(v,list) or isinstance(v,tuple):return [freeze(x) for x in v]
    if isinstance(v,dict):return {k:freeze(x) for k,x in v.items()}
    return v

def controls():
    base=Path('research/rmaf/results');passed=[]
    for filename in ['thesis-complexity-reachable-trace.json','thesis-complexity-three-credit-trace.json']:
        data=json.loads((base/filename).read_text());trace=data['trace'];f1=parse(trace[0]['F1']);f2=[parse(trace[0]['F2'])]
        for i,exp in enumerate(trace):
            f1,f2,r=normal(f1,f2,tuple(label(x) for x in exp['pair']))
            assert r['case']==exp['case'];assert set(r['pendants'])==set(map(label,exp['pendants']))
            assert protected([f1])==sorted(exp['protected_F1'])
            assert protected(f2)==sorted(exp['protected_F2'])
            for b,e in zip(r['branches'],exp['branches']):
                assert b['name']==e['name'] and b['legal']==e['legal'] and set(b['cuts'])==set(map(label,e['cuts']))
            if 'chosen_branch' in exp:f1,f2=child(f1,f2,next(b for b in r['branches'] if b['name']==exp['chosen_branch']))
        if len(trace)==3:
            f1,f2=child(f1,f2,next(b for b in r['branches'] if b['name']=='C'));_,_,r=normal(f1,f2)
            assert not any(b['legal'] for b in r['branches'])
        else:assert trace[-1]['P_Q_cardinalities']==[3,2]
        passed.append(filename)
    assert Fraction(1,4)+Fraction(1,8)+Fraction(3,16)==Fraction(9,16)
    fixtures=json.loads(Path('research/rmaf/thesis_complexity/repair/controls-frozen.json').read_text())['controls'][2:]
    for f in fixtures:
        t1=parse(f['F1']);t2=[parse(f['F2'])];mark([t1],map(label,f['protected_F1']));mark(t2,map(label,f['protected_F2']))
        try:state=normal(t1,t2,tuple(map(label,f['chosen_pair'])))
        except AssertionError:
            assert f['id']=='wrong-orientation';passed.append(f['id']);continue
        assert f['id']!='wrong-orientation'
        t1,t2,r=state;assert r['case']=='A3BC' and len(r['pendants'])==3
        t1,t2=child(t1,t2,next(b for b in r['branches'] if b['name']=='C'));t1,t2,r=normal(t1,t2)
        assert len(r['pendants'])==3
        if 'expected_C_legal_branches' in f:assert [b['name'] for b in r['branches'] if b['legal']]==f['expected_C_legal_branches']
        passed.append(f['id'])
    # Corruption detector with positive twin.
    assert legal([parse('(a,b)')],[label('a')]);bad=[parse('(a,b)')];mark(bad,[label('a')]);assert not legal(bad,[label('a')])
    return passed

def randtree(rng,labs):
    pool=[N(atoms=frozenset([x])) for x in labs]
    while len(pool)>1:
        a=pool.pop(rng.randrange(len(pool)));b=pool.pop(rng.randrange(len(pool)));pool.append(N(kids=[a,b]))
    return N(kids=pool,rho=True)

def mass(f1,f2,a,level=0):
    # Stop when a is merged or removed; all continuation is pessimistically free.
    if a not in ix([f1])[0]:return Fraction(1),0,[]
    if level>8:raise RuntimeError('local depth overflow')
    z=normal(copy.deepcopy(f1),copy.deepcopy(f2))
    if z is None:return Fraction(0),1,[]
    f1,f2,r=z
    if a not in ix([f1])[0]:return Fraction(1),0,[]
    val=Fraction(0);nodes=1;trace=[]
    for b in r['branches']:
        if not b['legal']:continue
        t1,t2=child(f1,f2,b)
        v,n,tr=mass(t1,t2,a,level+1);val+=v/Fraction(2**len(b['cuts']));nodes+=n
        trace.append({'rule':freeze(r),'branch':b['name'],'mass':str(v),'child':tr})
    return val,nodes,trace

def run(count,seed):
    rng=random.Random(seed);hits={3:0,4:0};maxima={3:Fraction(0),4:Fraction(0)};witnesses={};siblings=0
    for j in range(count):
        size=3+j%2;labs=['a','x','y']+(['z'] if size==3 else ['u','v'])+['p','q','r','s']
        outside=parse('((p,q),(r,s))').kids[0]
        local=parse('(a,((x,y),z))' if size==3 else '(a,((x,y),(u,v)))').kids[0]
        f1=N(kids=[N(kids=[local,outside])],rho=True);f2=[randtree(rng,labs)]
        ns,pa,_,_=ix(f2);a=label('a');b=sibling(ns,pa,a)
        if b is None:continue
        mark([f1],[a]);mark(f2,[a,b])
        try:z=normal(copy.deepcopy(f1),copy.deepcopy(f2),(label('x'),label('y')))
        except (AssertionError,KeyError):continue
        if z is None:continue
        f1,f2,r=z
        if r['case']!='A3BC' or len(r['pendants'])!=3 or not all(c['legal'] for c in r['branches']):continue
        if label('x')<=b:continue
        hits[size]+=1
        for bb in r['branches']:
            if bb['legal']:
                pmap=ix(f2)[1];assert len({pmap[k] for k in bb['cuts']})==len(bb['cuts']);siblings+=1
        t1,t2=child(f1,f2,r['branches'][-1]);v,n,tr=mass(t1,t2,a)
        if v>maxima[size] or size not in witnesses:
            maxima[size]=v;witnesses[size]={'F1':f1.text(),'F2':[t.text() for t in f2],'b':freeze(b),'mass':str(v),'nodes':n,'trace':tr}
        if v>Fraction(1,4):return {'status':'FIRE','index':j,'hits':hits,'maxima':{k:str(v) for k,v in maxima.items()},'witnesses':witnesses}
    return {'status':'NO-FIRE-BOUNDED','geometries':count,'hits':hits,'maxima':{k:str(v) for k,v in maxima.items()},'source_cut_checks':siblings,'witnesses':witnesses}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--count',type=int,default=100);ap.add_argument('--seed',type=int,default=614);ap.add_argument('--out',required=True);args=ap.parse_args();start=time.perf_counter()
    cs=controls();res=run(args.count,args.seed);res.update(controls=cs,elapsed_seconds=time.perf_counter()-start,seed=args.seed,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    p=Path(args.out);tmp=p.with_suffix('.tmp');tmp.write_text(json.dumps(res,indent=2)+'\n');tmp.replace(p)
    print(json.dumps({k:v for k,v in res.items() if k!='witnesses'}))
