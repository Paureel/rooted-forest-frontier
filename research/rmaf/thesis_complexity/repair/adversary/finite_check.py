#!/usr/bin/env python3
"""One-shot independent adversary instrument; source rules, no project evaluator imports.
Output is finite control/search evidence, never a proof of a universal runtime bound.
See SPEC.md for inputs, failure meaning, controls, and search interpretation.
"""
from __future__ import annotations
import argparse, copy, itertools, json, random, time
from pathlib import Path
from fractions import Fraction

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
class N:
    def __init__(self, kids=(), lab=None, prot=False):
        self.kids=list(kids); self.lab=frozenset(lab) if lab else None; self.prot=prot; self.par=None
        for v in self.kids:v.par=self
    def leaves(self):
        return (self.lab or frozenset()) | frozenset().union(*(c.leaves() for c in self.kids))
    def key(self):return ','.join(sorted(self.leaves()))
    def sig(self):return ('L',tuple(sorted(self.lab))) if self.lab else ('N',tuple(sorted((c.sig() for c in self.kids),key=repr)))
    def depth(self):return 0 if self.par is None else self.par.depth()+1
    def sibling(self):
        return next((c for c in self.par.kids if c is not self),None) if self.par else None
    def top(self):return self if self.par is None else self.par.top()
    def walk(self):
        yield self
        for c in self.kids:yield from c.walk()
    def text(self):
        s='('+','.join(c.text() for c in self.kids)+')' if self.kids else ''
        return s+('&'.join(sorted(self.lab)) if self.lab else '')

def parse(s):
    s=s.strip(); pos=0
    def rec():
        nonlocal pos
        if s[pos]=='(':
            pos+=1; kids=[rec()]
            while s[pos]==',':pos+=1;kids.append(rec())
            assert s[pos]==')';pos+=1
            start=pos
            while pos<len(s) and s[pos] not in '(),':pos+=1
            lab=s[start:pos]
            return N(kids, [lab] if lab else None)
        start=pos
        while pos<len(s) and s[pos] not in '(),':pos+=1
        return N(lab=[s[start:pos]])
    t=rec();assert pos==len(s)
    if t.lab!=frozenset(['rho']):t=N([t],['rho'])
    return [t]

def nodes(f):return [n for t in f for n in t.walk()]
def lookup(f,key):return next(n for n in nodes(f) if n.key()==key)
def mark(f,keys):
    for k in keys:lookup(f,k).prot=True

def clades(f):return sorted(n.key() for n in nodes(f) if n.prot and n.par is not None)
def active(f):return [n for n in nodes(f) if n.lab and not n.kids and n.lab!=frozenset(['rho'])]
def matching(f,n):return next((v for v in nodes(f) if v.sig()==n.sig()),None)
def allowed(v):
    if v.par is None or v.prot:return False
    s=v.sibling()
    return not (v.par.par is None and s is not None and s.prot)
def cut(f,keys,check=True):
    f=copy.deepcopy(f); vs=[lookup(f,k) for k in keys]
    if check:assert all(allowed(v) for v in vs),('illegal cut',keys)
    for v in vs:
        v.par.kids.remove(v);v.par=None;v.prot=False;f.append(v)
    def norm(v):
        kids=[w for c in v.kids if (w:=norm(c)) is not None]
        v.kids=kids
        for c in kids:c.par=v
        if v.lab:return v
        if len(kids)==0:return None
        if len(kids)==1:
            w=kids[0];w.prot=w.prot or v.prot;w.par=v.par;return w
        return v
    out=[]
    for t in f:
        t=norm(t)
        if t is not None:t.par=None;t.prot=False;out.append(t)
    return out

def pathdata(a,c):
    if a.top() is not c.top():return None,[]
    ach=[];x=a
    while x is not None:ach.append(x);x=x.par
    cch=[];x=c
    while x not in ach:cch.append(x);x=x.par
    lca=x; aseg=ach[:ach.index(lca)]
    pend=[n.sibling() for n in aseg[:-1]]+[n.sibling() for n in reversed(cch[:-1])]
    return lca,pend

def candidates(f1,f2):
    ns=nodes(f1);ps=[n.par for n in ns if n.prot and n.par]
    region=max(ps,key=lambda n:n.depth()) if ps else f1[0]
    eligible=[v for v in region.walk() if len(v.kids)==2 and all(c.lab and not c.kids for c in v.kids)]
    if not eligible:return []
    def rank(v):
        a,c=[matching(f2,n) for n in v.kids]
        return (v.depth(), a.top() is not c.top(), max(a.depth(),c.depth()))
    best=max(map(rank,eligible));out=[]
    for v in eligible:
        if rank(v)==best:
            a,c=[matching(f2,n) for n in v.kids]
            if a.top() is not c.top() or a.depth()==c.depth():out.extend([(v.kids[0].key(),v.kids[1].key()),(v.kids[1].key(),v.kids[0].key())])
            elif a.depth()>c.depth():out.append((v.kids[0].key(),v.kids[1].key()))
            else:out.append((v.kids[1].key(),v.kids[0].key()))
    return out

def describe(f1,f2,pair,validate=True):
    if validate:assert tuple(pair) in candidates(f1,f2),('orientation/depth',pair,candidates(f1,f2))
    a,c=[lookup(f2,k) for k in pair]; A,C=[lookup(f1,k) for k in pair]
    assert A.par is C.par
    u=A.par.sibling(); lca,pend=pathdata(a,c);q=len(pend)
    branches=[]
    def add(name,vs,p1=(),p2=()):branches.append(dict(name=name,cuts=[v.key() for v in vs],protect1=[v.key() for v in p1],protect2=[v.key() for v in p2],legal=all(allowed(v) for v in vs)))
    if a.par is None or c.par is None:return dict(case='ROOT',pair=pair,pendants=[],branches=[])
    if a.par is c.par:return dict(case='MERGE',pair=pair,pendants=[],branches=[])
    case=None
    if lca is None:case='AC';add('A',[a]);add('C',[c])
    elif q==1:case='B';add('B',pend)
    elif u is not None and a.sibling() is not None and a.sibling().sig()==u.sig():case='RB';add('C',[c])
    elif u is not None and c.sibling() is not None and c.sibling().sig()==u.sig():case='RB';add('A',[a])
    else:
        # RB*: the pendant caterpillar is exactly the F1 uncle subtree.
        chain=None
        if q>=2:
            chain=N([copy.deepcopy(pend[0]),copy.deepcopy(pend[1])])
            for p in pend[2:]:chain=N([chain,copy.deepcopy(p)])
        if c.par is lca and u is not None and chain and chain.sig()==u.sig():case='RB*';add('A',[a])
        elif q==2 and u is not None and lca.sibling() is not None and lca.sibling().sig()==u.sig():case='2B';add('B',pend)
        else:
            u2=matching(f2,u) if u else None
            if q>=2 and u2 is not None and u2.prot and u2.par is pend[0]:
                case='BCY';add('B',pend);add('CY',[c,u2.sibling()])
            elif q==2:
                case='A2BC'
                if not c.prot:add('A',[a]);add('B',pend);add('C',[c],[A],[a]+pend)
                else:add('B',pend);add('A',[a],[],pend)
            elif q>=3:case='A3BC';add('A',[a]);add('B',pend);add('C',[c],[A],[a])
    assert case is not None
    return dict(case=case,pair=list(pair),pendants=[n.key() for n in pend],branches=branches)

def step(f1,f2,branch):
    f1=copy.deepcopy(f1);f2=copy.deepcopy(f2)
    mark(f1,branch['protect1']);mark(f2,branch['protect2']);f2=cut(f2,branch['cuts'])
    return f1,f2

def normalize(f1,f2):
    f1=copy.deepcopy(f1);f2=copy.deepcopy(f2)
    while True:
        choices=candidates(f1,f2)
        if not choices:return f1,f2
        a,c=[lookup(f2,k) for k in choices[0]];A,C=[lookup(f1,k) for k in choices[0]]
        if a.par is c.par and a.par is not None:
            for p in [A.par,a.par]:
                p.lab=A.lab|C.lab;p.kids=[]
        elif a.par is None or c.par is None:
            v=A if a.par is None else C; v2=a if a.par is None else c
            f1=cut(f1,[v.key()],check=False)
            f1=[t for t in f1 if t.key()!=v.key()]; f2=[t for t in f2 if t is not v2]
        else:return f1,f2

def state(t1,t2,p1=(),p2=()):
    f1=parse(t1);f2=parse(t2);mark(f1,p1);mark(f2,p2);return f1,f2

def exact_control():
    controls=json.loads((HERE.parent/'controls-frozen.json').read_text())
    res=[]
    # Frozen local positive, negative, and passing twin share the production evaluator.
    for spec in controls['controls'][2:]:
        f1,f2=state(spec['F1'],spec['F2'],spec['protected_F1'],spec['protected_F2'])
        pair=spec['chosen_pair']; accepted=tuple(pair) in candidates(f1,f2)
        assert accepted==spec.get('expected_orientation_accepted',True)
        d=describe(f1,f2,pair,validate=accepted)
        C=next(b for b in d['branches'] if b['name']=='C')
        g1,g2=normalize(*step(f1,f2,C)); nxt=describe(g1,g2,candidates(g1,g2)[0])
        want=spec.get('expected_C_pendants',spec.get('if_illegally_cut_y_expected_C_pendants'))
        assert len(nxt['pendants'])==want,(spec['id'],nxt)
        if spec['id']=='live-two-leaf':
            assert d['case']=='A3BC' and len(d['pendants'])==3
            assert [b['name'] for b in nxt['branches'] if b['legal']]==['B']
        res.append(dict(id=spec['id'],orientation_accepted=accepted,parent=d,C=nxt))
    for file in ['thesis-complexity-reachable-trace.json','thesis-complexity-three-credit-trace.json']:
        cert=json.loads((ROOT/'results'/file).read_text());tr=cert['trace'];checks=[]
        f1,f2=state(tr[0]['F1'],tr[0]['F2']);P=set();Q=set()
        for i,s in enumerate(tr):
            assert sorted(clades(f1))==sorted(s['protected_F1'])
            assert sorted(clades(f2))==sorted(s['protected_F2'])
            d=describe(f1,f2,s['pair'])
            assert d['case']==s['case'] and d['pendants']==s['pendants'],(file,i,d)
            for b,expected in zip(d['branches'],s['branches']):
                assert b==expected,(file,i,b,expected)
            assert [len(P),len(Q)]==s['P_Q_cardinalities']
            checks.append(d)
            if s.get('chosen_branch'):
                b=next(b for b in d['branches'] if b['name']==s['chosen_branch']);assert b['legal']
                if i==0:P={s['pair'][0]};Q=set()
                elif i==1:pass # G3 retained-credit branch, source p120.
                else:P.add(s['pair'][0]);Q.add(s['pair'][0]) # p123 G4 unions.
                f1,f2=normalize(*step(f1,f2,b))
        if len(tr)==3:
            b=next(b for b in checks[-1]['branches'] if b['name']=='C')
            g1,g2=normalize(*step(f1,f2,b));out=describe(g1,g2,candidates(g1,g2)[0]);assert not any(b['legal'] for b in out['branches'])
            checks.append(out)
        else:assert (len(P),len(Q))==(3,2)
        res.append(dict(id='nine-leaf' if len(tr)==3 else 'thirteen-leaf',trace=checks,P=sorted(P),Q=sorted(Q)))
    mass=Fraction(1,4)+Fraction(1,8)+Fraction(3,16)
    assert mass==Fraction(9,16)>Fraction(1,2)
    # Null and mutation controls.
    f=parse('(a,(x,y))');assert cut(f,[])[0].text()==f[0].text()
    mark(f,['a','x,y']);assert not allowed(lookup(f,'a'))
    g=cut(f,['x']);assert lookup(g,'y').prot and lookup(g,'a').sibling().key()=='y'
    f=[N([N(lab=['a'],prot=True),N(lab=['b'])])];assert not allowed(lookup(f,'b'))
    rejected=0
    # Corrupt an expected pendant count, then corrupt the incoming x protection.
    try:assert len(res[0]['C']['pendants'])==2
    except AssertionError:rejected+=1
    spec=controls['controls'][2]
    f1,f2=state(spec['F1'],spec['F2'],spec['protected_F1'],spec['protected_F2'])
    mark(f2,['x'])
    damaged=describe(f1,f2,spec['chosen_pair'])
    try:assert all(b['legal'] for b in damaged['branches'])
    except AssertionError:rejected+=1
    assert rejected==2
    return dict(controls=res,arithmetic=dict(child_mass=str(mass),parent_mass='1/2'),mutation_catches=rejected)

def randtree(labels,rng):
    pool=[N(lab=[x]) for x in labels]
    while len(pool)>1:
        a=pool.pop(rng.randrange(len(pool)));b=pool.pop(rng.randrange(len(pool)));pool.append(N([a,b]))
    return pool[0]

def local_search(limit,seed):
    rng=random.Random(seed);count=eligible=live=dead=0;hist=0;fires=[];start=time.monotonic()
    for i in range(limit):
        n=6+i%3;extras=[f'p{j}' for j in range(n-3)]
        f1=[N([N([N(lab=['a']),N([N(lab=['x']),N(lab=['y'])])]),randtree(extras,rng)])]
        f1=[N(f1,['rho'])];mark(f1,['a'])
        f2=[N([randtree(['a','x','y']+extras,rng)],['rho'])]
        a=lookup(f2,'a');s=a.sibling()
        if s is None:continue
        a.prot=s.prot=True;count+=1
        # history persistence: every legal singleton cut that leaves a active.
        for v in nodes(f2):
            if allowed(v) and 'a' not in v.leaves():
                g=cut(f2,[v.key()]);aa=lookup(g,'a');ss=aa.sibling();hist+=1
                if aa.par is None or ss is None or not ss.prot:
                    fires.append(dict(kind='history',F2=f2[0].text(),cut=v.key()))
                    return dict(attempts=i+1,eligible=eligible,live=live,dead=dead,history_checks=hist,fires=fires,seconds=time.monotonic()-start)
        for pair in candidates(f1,f2):
            if set(pair)!={'x','y'}:continue
            d=describe(f1,f2,pair)
            if d['case']!='A3BC' or len(d['pendants'])!=3 or not all(b['legal'] for b in d['branches']):continue
            eligible+=1;C=next(b for b in d['branches'] if b['name']=='C')
            g1,g2=normalize(*step(f1,f2,C));opts=candidates(g1,g2)
            for pair2 in opts:
                dd=describe(g1,g2,pair2);bs=[b for b in dd['branches'] if b['legal']]
                if bs:live+=1
                else:dead+=1
                if set(pair2)!={'a',pair[0]} or any(len(b['cuts'])<3 or b['name']!='B' for b in bs):
                    fires.append(dict(kind='local',F1=f1[0].text(),F2=f2[0].text(),J=d,C=dd))
                    return dict(attempts=i+1,eligible=eligible,live=live,dead=dead,history_checks=hist,fires=fires,seconds=time.monotonic()-start)
    return dict(attempts=limit,eligible=eligible,live=live,dead=dead,history_checks=hist,fires=fires,seconds=time.monotonic()-start)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--search',type=int,default=0);ap.add_argument('--seed',type=int,default=41017);ap.add_argument('--output',required=True);args=ap.parse_args()
    start=time.monotonic();out={'schema_version':1,'independence':'fresh graph evaluator; no project evaluator imported','control':exact_control()}
    print('CONTROLS PASS: 5 frozen fixtures, 2 comparator mutation catches',flush=True)
    if args.search:out['search']=local_search(args.search,args.seed);print(json.dumps(out['search']),flush=True)
    out['elapsed_seconds']=time.monotonic()-start
    Path(args.output).write_text(json.dumps(out,indent=2)+'\n')
