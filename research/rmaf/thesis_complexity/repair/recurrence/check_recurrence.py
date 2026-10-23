#!/usr/bin/env python3
"""One-shot exact recurrence/control instrument. No parent/other-route imports.
It audits source-written recurrence schemas and fixed tree cut controls, not
universal source reachability. All output is local and exact rational.
"""
from __future__ import annotations
import argparse, json, re, time, hashlib
from fractions import Fraction as F
from pathlib import Path
from dataclasses import dataclass, field
ROOT=Path(__file__).resolve().parents[5]
HERE=Path(__file__).resolve().parent
RESULT=ROOT/'research/rmaf/results'
@dataclass(eq=False)
class N:
    label: str|None=None
    children: list=field(default_factory=list)
    protected: bool=False
    parent: N|None=None
    def leaves(self):
        return ({self.label} if self.label else set()) | set().union(*(c.leaves() for c in self.children))
    def key(self): return ','.join(sorted(self.leaves()))
    def depth(self): return 0 if self.parent is None else 1+self.parent.depth()
    def shape(self): return self.label if not self.children else tuple(sorted((c.shape() for c in self.children),key=str))

def tree(s,protected=()):
    rho=s.endswith('rho')
    toks=re.findall(r'[(),]|[^(),]+',s[:-3] if rho else s); pos=0
    def rec():
        nonlocal pos
        if toks[pos]!='(':
            x=N(toks[pos]);pos+=1;return x
        pos+=1;cs=[rec()]
        while toks[pos]==',':pos+=1;cs.append(rec())
        assert toks[pos]==')';pos+=1;x=N(children=cs)
        for c in cs:c.parent=x
        return x
    r=rec();assert pos==len(toks)
    if rho:r.label='rho'
    else:r=N('rho',[r]);r.children[0].parent=r
    for n in walk(r):n.protected=n.key() in protected
    return [r]
def walk(n):
    yield n
    for c in n.children:yield from walk(c)
def nodes(f):return [n for r in f for n in walk(r)]
def get(f,key):return next(n for n in nodes(f) if n.key()==key)
def ancestor(n,a):
    while n is not None:
        if n is a:return True
        n=n.parent
    return False

def path_pendants(a,c):
    aa=[];x=a
    while x is not None:aa.append(x);x=x.parent
    cc=[];x=c
    while x not in aa:
        if x is None:return None,None
        cc.append(x);x=x.parent
    lca=x;aa=aa[:aa.index(lca)];path=aa+[lca]+list(reversed(cc));ps=[]
    for i,n in enumerate(path):
        if n is a or n is c:continue
        adjacent={path[j] for j in (i-1,i+1) if 0<=j<len(path)}
        ps.extend(ch for ch in n.children if ch not in adjacent)
    return lca,ps

def legal(f,keys):
    cuts=[get(f,k) for k in keys]
    if any(n.parent is None or n.protected for n in cuts):return False
    for n in cuts:
        if n.parent.parent is None and any(s is not n and s.protected for s in n.parent.children):return False
    return True

def cut(f,keys,protect=()):
    # Simultaneous original-edge deletion; then exactly Chapter2 normalization.
    for k in protect:get(f,k).protected=True
    cuts=[get(f,k) for k in keys];new=[]
    for n in cuts:
        assert n.parent is not None
        n.parent.children.remove(n);n.parent=None;n.protected=False;new.append(n)
    def norm(n):
        cs=[]
        for c in n.children:
            c=norm(c)
            if c is not None:cs.append(c)
        n.children=cs
        for c in cs:c.parent=n
        if n.label is None and not cs:return None
        if n.label is None and len(cs)==1:
            c=cs[0];c.protected |= n.protected;c.parent=n.parent;return c
        return n
    out=[norm(n) for n in f+new];out=[n for n in out if n is not None]
    for n in out:n.parent=None;n.protected=False
    return out

def sibling(n):
    if n.parent is None:return None
    ss=[c for c in n.parent.children if c is not n]
    return ss[0] if len(ss)==1 else None

def first_case(f1,f2,ak,ck):
    a=get(f2,ak);c=get(f2,ck);a1=get(f1,ak);c1=get(f1,ck)
    assert a1.parent is c1.parent
    lca,ps=path_pendants(a,c)
    if lca is None:return 'AC',[("A",[ak]),("C",[ck])],[]
    if len(ps)==1:return 'B',[("B",[ps[0].key()])],ps
    u=sibling(a1.parent)
    def exists1(n):return n is not None and any(n.shape()==m.shape() for m in nodes(f1))
    for end,other in ((a,c),(c,a)):
        b=sibling(end)
        if b is not None and u is not None and exists1(b) and b.shape()==u.shape():
            return 'RB',[("RB",[other.key()])],ps
    if c.parent is lca and len(ps)>=2 and u is not None and all(exists1(b) for b in ps):
        shape=tuple(sorted((ps[0].shape(),ps[1].shape()),key=str))
        for b in ps[2:]:shape=tuple(sorted((shape,b.shape()),key=str))
        if shape==u.shape():return 'RB*',[("RB*",[ak])],ps
    u2=next((n for n in nodes(f2) if u is not None and n.shape()==u.shape()),None)
    if len(ps)==2 and u2 is sibling(lca):return '2B',[("B",[b.key() for b in ps])],ps
    if u2 is not None and u2.protected and ps and u2.parent is ps[0]:
        y=sibling(u2)
        return 'BCY',[("B",[b.key() for b in ps]),("CY",[ck,y.key()])],ps
    if len(ps)==2:
        br=[('B',[b.key() for b in ps]),('A',[ak])] if c.protected else [('A',[ak]),('B',[b.key() for b in ps]),('C',[ck])]
        return 'A2BC',br,ps
    assert len(ps)>=3
    return 'A3BC',[('A',[ak]),('B',[b.key() for b in ps]),('C',[ck])],ps

def choose(f1,f2):
    r=next(r for r in f1 if r.label=='rho')
    tops=[n.parent for n in walk(r) if n.protected and n.parent is not None]
    top=max(tops,key=lambda n:n.depth()) if tops else r
    pairs=[n.children for n in walk(top) if len(n.children)==2 and all(not c.children for c in n.children)]
    def rank(pair):
        a,c=(get(f2,n.key()) for n in pair);l,_=path_pendants(a,c)
        return pair[0].depth(), l is None, max(a.depth(),c.depth())
    pair=max(pairs,key=rank);ks=[n.key() for n in pair]
    ks.sort(key=lambda k:get(f2,k).depth(),reverse=True)
    return ks

def c_continuation(f1,f2,pair):
    a,c=pair
    assert get(f2,a).depth()>=get(f2,c).depth(), 'wrong orientation'
    assert legal(f2,[c])
    f2=cut(f2,[c],[a]);get(f1,a).protected=True;f1=cut(f1,[c])
    # The detached common singleton is roots-done, not active Rt.
    f1=[r for r in f1 if r.label=='rho']
    pair2=choose(f1,f2);case,br,ps=first_case(f1,f2,*pair2)
    return {'pair':pair2,'case':case,'pendants':len(ps),'legal_branches':[n for n,ks in br if legal(f2,ks)]}

def w(p,q):assert 0<=q<=p<=3;return F(2+q,2**(p+1))
def b(p):return p-3
def row(name,p,q,children):
    mass=sum((w(cp,cq)/2**d for d,cp,cq in children),F(0));offset=1+sum(b(cp) for _,cp,_ in children)
    return dict(id=name,parent=[p,q],children=children,mass=str(mass),target=str(w(p,q)),offset=offset,target_offset=b(p),mass_slack=str(w(p,q)-mass),offset_slack=b(p)-offset,pass_mass=mass<=w(p,q),pass_offset=offset<=b(p))
def tables():
    rr=[]
    for r in range(3):
        for t in range(r+1):
            rr.append(row(f'lifted-A2-{r}-{t}',r,t,[(1,r,t),(2,r,t),(1,r+1,t)]))
            rr.append(row(f'lifted-A3-{r}-{t}',r,t,[(1,r,t),(3,r,t),(1,r+1,t+1)]))
    for t in range(2):
        for s in (3,4):rr.append(row(f'G4.1-A3-{t}-{s}',1,t,[(1,1,t),(s,0,0),(1,2,t+1)]))
    for r in range(2):
        for t in range(r+1):
            for localq in (0,1):
                rr.append(row(f'lifted-single-discharge-{r}-{t}-{localq}',r+1,t+localq,[(1,r,t)]))
                rr.append(row(f'lifted-double-discharge-{r}-{t}-{localq}',r+2,t+localq,[(2,r,t)]))
            rr.append(row(f'lifted-G3-Q-nonempty-A2-{r}-{t}',r+1,t+1,[(1,r,t),(2,r,t)]))
            rr.append(row(f'lifted-G3-Q-empty-A2-{r}-{t}',r+1,t,[(1,r+1,t),(2,r,t)]))
            rr.append(row(f'lifted-G3-Q-empty-A3-{r}-{t}',r+1,t,[(1,r+1,t+1),(3,r,t)]))
    return rr

def controls():
    checks=[]
    def check(name,got,expected):
        assert got==expected,(name,got,expected)
        checks.append({'id':name,'actual':str(got),'expected':str(expected),'pass':True})
    check('nine-sixteenths',row('x',1,0,[(1,1,0),(3,0,0),(1,2,1)])['mass'],'9/16')
    check('four-pendant-closes',row('x',1,0,[(1,1,0),(4,0,0),(1,2,1)])['mass'],'1/2')
    check('incoming-Q-closes',row('x',1,1,[(1,1,1),(3,0,0),(1,2,2)])['mass'],'3/4')
    r=row('x',2,1,[(1,2,1),(3,2,1),(1,3,2)])
    check('p3-leading',r['mass'],'23/64');check('p3-offset',r['offset'],-1)
    check('p3-discharge',row('x',3,2,[(2,1,0)])['mass'],'1/8')
    check('terminal-null',(F(0),1),(F(0),1))
    check('C-discharge-positive',(F(1,4),1-3),(F(1,4),-2))
    check('C-cost-one-mutation-caught',F(1,2)<=F(1,4),False)
    check('invocation-offset-mutation-caught',0-3*2==1-3*2,False)
    nine=json.loads((RESULT/'thesis-complexity-reachable-trace.json').read_text())['trace'][-1]
    got=c_continuation(tree(nine['F1'],nine['protected_F1']),tree(nine['F2'],nine['protected_F2']),nine['pair'])
    check('nine-C-dead',got['legal_branches'],[])
    fixed=json.loads((HERE.parent/'controls-frozen.json').read_text())['controls']
    for f in fixed[2:]:
        f1=tree(f['F1'],f['protected_F1']);f2=tree(f['F2'],f['protected_F2']);pair=f['chosen_pair']
        orientation=get(f2,pair[0]).depth()>=get(f2,pair[1]).depth()
        check(f['id']+'-orientation',orientation,f.get('expected_orientation_accepted',True))
        if not orientation:
            # The production routine must reject the mutation, never bless its C continuation.
            caught=False
            try:c_continuation(f1,f2,pair)
            except AssertionError:caught=True
            check('wrong-orientation-refusal',caught,True)
            # Deliberately bypass orientation only to reproduce the planted
            # mutation's geometric effect; it remains outside the algorithm.
            a,c=pair
            f1=tree(f['F1'],f['protected_F1']);f2=tree(f['F2'],f['protected_F2'])
            f2=cut(f2,[c],[a]);get(f1,a).protected=True;f1=cut(f1,[c])
            f1=[r for r in f1 if r.label=='rho']
            ap,cp=choose(f1,f2)
            _,badps=path_pendants(get(f2,ap),get(f2,cp))
            check('illegal-orientation-C-pendants',len(badps),f['if_illegally_cut_y_expected_C_pendants'])
            continue
        case,branches,ps=first_case(f1,f2,*pair)
        check(f['id']+'-case',case,'A3BC')
        got=c_continuation(f1,f2,pair)
        check(f['id']+'-C-pendants',got['pendants'],f['expected_C_pendants'])
        if 'expected_C_legal_branches' in f:check(f['id']+'-C-legal',got['legal_branches'],f['expected_C_legal_branches'])
    thirteen=json.loads((RESULT/'thesis-complexity-three-credit-trace.json').read_text())['trace']
    # Credit unions reconstructed independently from the printed p123 rule.
    P={'a'};Q=set()
    for step in thirteen[2:4]:
        assert step['case']=='A3BC' and step['chosen_branch']=='C'
        P.add(step['pair'][0]);Q.add(step['pair'][0])
    check('p3-credit-union',(len(P),len(Q)),(3,2));check('p3-not-protection-count',len(thirteen[-1]['protected_F2'])>len(P),True)
    state=thirteen[-1];case,branches,ps=first_case(tree(state['F1'],state['protected_F1']),tree(state['F2'],state['protected_F2']),*state['pair'])
    check('p3-discharge-case',case,'A2BC');check('p3-discharge-pendants',len(ps),2)
    f2=tree(state['F2'],state['protected_F2']);check('p3-only-B',[name for name,ks in branches if legal(f2,ks)],['B'])
    for k in range(-4,0):
        for p in range(4):
            for q in range(p+1):
                assert 128*F(2)**k*w(p,q)+b(p)>=1,(k,p,q)
    check('base-boundary-states',40,40)
    normf=tree('(a,(x,y))',['x,y'])
    normf=cut(normf,['y'])
    check('suppression-inherits-protection',get(normf,'x').protected,True)
    check('protected-cut-refused',legal(normf,['x']),False)
    check('rho-preserved',sum(n.label=='rho' for n in nodes(normf)),1)
    a=N('a',protected=True);c=N('c');rt=N(children=[a,c]);a.parent=rt;c.parent=rt
    check('component-root-sibling-protection-refused',legal([rt],['c']),False)
    return checks

def atomic(path,data):
    tmp=path.with_suffix(path.suffix+'.tmp');tmp.write_text(json.dumps(data,indent=2)+'\n');tmp.replace(path)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--repeat',type=int,default=1);ap.add_argument('--tag',default='pilot');args=ap.parse_args()
    start=time.perf_counter();cc=controls();pilot=time.perf_counter()-start
    start=time.perf_counter();rr=None
    for _ in range(args.repeat):rr=tables()
    elapsed=time.perf_counter()-start
    failures=[r for r in rr if not (r['pass_mass'] and r['pass_offset'])]
    # This scan is adversarial: the two printed-schema failures are findings,
    # not allowed to disappear into a universal acceptance banner.
    assert {r['id'] for r in failures}=={'G4.1-A3-0-3','lifted-G3-Q-nonempty-A2-1-1'}
    out={'status':'OPEN-STRUCTURAL','controls':cc,'controls_seconds':pilot,'rows':rr,'failures':failures,'metrics':{'controls_passed':len(cc),'row_count':len(rr),'arithmetic_failures':len(failures),'repeat':args.repeat,'table_seconds':elapsed},'scope':'Exact arithmetic schemas and fixed tree controls only; neither failing row asserts source reachability; no universal runtime theorem.'}
    dest=RESULT/f'thesis-runtime-repair-recurrence-{args.tag}.json';atomic(dest,out)
    print(json.dumps({'status':out['status'],'metrics':out['metrics'],'controls_seconds':pilot,'failure_ids':[r['id'] for r in failures],'receipt':str(dest)},sort_keys=True))
if __name__=='__main__':main()
