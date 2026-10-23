#!/usr/bin/env python3
"""One-shot nonauthor source/control replay. No prior checker imports.
Tree vertices carry protection on their incoming attachment. Batch cuts use the
original vertices and are checked before any suppression. Exact Fraction algebra.
"""
from dataclasses import dataclass, field
from fractions import Fraction as F
from pathlib import Path
from copy import deepcopy
import json,re,time,hashlib,sys
ROOT=Path(__file__).resolve().parents[4]
OUT=ROOT/'results/thesis-runtime-repair-fresh-review-history-controls.json'

@dataclass(eq=False)
class N:
    name:str=''
    ch:list=field(default_factory=list)
    protected:bool=False
    def labels(self):
        return frozenset([self.name]) if not self.ch else frozenset().union(*(c.labels() for c in self.ch))
    def key(self): return ','.join(sorted(self.labels()))

def parse(s):
    tokens=re.findall(r'[A-Za-z0-9_]+|[(),]',s); pos=0
    def rec():
        nonlocal pos
        if tokens[pos]!='(':
            ans=N(tokens[pos]);pos+=1;return ans
        pos+=1; kids=[rec()]
        while tokens[pos]==',':pos+=1;kids.append(rec())
        assert tokens[pos]==')';pos+=1
        return kids[0] if len(kids)==1 else N(ch=kids)
    t=rec()
    if pos<len(tokens):assert tokens[pos]=='rho';pos+=1
    assert pos==len(tokens)
    return N('rho',[t])

def index(forest):
    by={};par={};dep={};comp={}
    def rec(n,p,d,r):
        # rho has same leaf cluster as its only child; exclude it from key map.
        if n.name!='rho':by[n.key()]=n
        par[n]=p;dep[n]=d;comp[n]=r
        for c in n.ch:rec(c,n,d+1,r)
    for r in forest:rec(r,None,0,r)
    return by,par,dep,comp

def sibling(n,par):
    p=par[n]
    return next((x for x in p.ch if x is not n),None) if p is not None else None

def cut_batch(forest,cutkeys,extra=(),check=True):
    forest=deepcopy(forest);by,par,_,_=index(forest)
    cuts={by[k] for k in cutkeys}
    if check:
        for n in cuts:
            assert par[n] is not None,'root cut'
            assert not n.protected,'protected cut'
            p=par[n];s=sibling(n,par)
            assert not(par[p] is None and s and s.protected),'protected root sibling'
    for k in extra:by[k].protected=True
    detached=[]
    def walk(n,asroot=False):
        if n in cuts and not asroot:
            detached.append(walk(n,True));return None
        kids=[z for c in n.ch if (z:=walk(c)) is not None]
        if not n.ch:return n
        if n.name=='rho':n.ch=kids;return n
        if not kids:return None
        if len(kids)==1:
            z=kids[0];z.protected=z.protected or n.protected;return z
        n.ch=kids;return n
    result=[z for n in forest if (z:=walk(n)) is not None]+detached
    for n in result:n.protected=False
    return result

@dataclass
class State:
    t:N
    f:list
    def idx(self):return index([self.t]),index(self.f)
    def active(self):return len(self.t.labels())+1

def set_prot(st,p1,p2):
    i,j=st.idx()
    for k in p1:i[0][k].protected=True
    for k in p2:j[0][k].protected=True
    return st

def choices(st):
    (b1,p1,d1,_),(b2,p2,d2,c2)=st.idx()
    protected=[x for x in p1 if x.protected and p1[x] is not None]
    limit=max((p1[x] for x in protected),key=lambda n:d1[n],default=st.t)
    def below(x):
        while x is not None:
            if x is limit:return True
            x=p1[x]
        return False
    pairs=[]
    for n in p1:
        if len(n.ch)==2 and all(not x.ch for x in n.ch) and below(n):
            a,c=n.ch;aa,cc=b2[a.key()],b2[c.key()]
            rank=(d1[a],int(c2[aa] is not c2[cc]),max(d2[aa],d2[cc]))
            pair=(a.key(),c.key()) if d2[aa]>=d2[cc] else (c.key(),a.key())
            pairs.append((rank,pair))
    if not pairs:return []
    m=max(rank for rank,p in pairs)
    return [p for rank,p in pairs if rank==m]

def normalize(st):
    st=deepcopy(st)
    while st.active()>2:
        pairs=choices(st)
        assert pairs,'no eligible pair'
        # only arbitrary ties chosen; report explicitly if this matters.
        a,c=pairs[0];(b1,p1,_,_),(b2,p2,_,_)=st.idx();aa,cc=b2[a],b2[c]
        if p2[aa] is p2[cc] and p2[aa] is not None:
            n1=p1[b1[a]];n2=p2[aa];name='['+'|'.join(sorted([a,c]))+']'
            n1.ch=[];n1.name=name;n2.ch=[];n2.name=name
        elif p2[aa] is None or p2[cc] is None:
            x=a if p2[aa] is None else c
            roots=cut_batch([st.t],[x],check=False)
            st.t=next(r for r in roots if r.name=='rho')
            st.f=[r for r in st.f if r.key()!=x]
        else:return st
    return st

def path_info(st,a,c):
    _,(by,par,dep,comp)=st.idx();u,v=by[a],by[c]
    if comp[u] is not comp[v]:return None,[]
    au=[];x=u
    while x is not None:au.append(x);x=par[x]
    av=[];x=v
    while x not in au:av.append(x);x=par[x]
    lca=x;left=au[:au.index(lca)]
    pend=[]
    for x in left[:-1]:pend.append(sibling(x,par))
    for x in reversed(av[:-1]):pend.append(sibling(x,par))
    return lca,[n for n in pend if n is not None]

def classify(st,pair,require_orientation=True):
    a,c=pair;(b1,p1,d1,_),(b2,p2,d2,comp)=st.idx()
    assert a in b1 and c in b1 and p1[b1[a]] is p1[b1[c]],'not sibling pair'
    assert any(set(pair)==set(x) for x in choices(st)),'depth selection'
    assert not require_orientation or d2[b2[a]]>=d2[b2[c]],'wrong orientation'
    u,v=b2[a],b2[c];lca,pend=path_info(st,a,c)
    uncle=sibling(p1[b1[a]],p1)
    uk=uncle.key() if uncle else None
    sb=sibling(u,p2);sd=sibling(v,p2)
    specs=[]
    def branch(name,cs,pp2=(),pp1=()):specs.append(dict(name=name,cuts=list(cs),protect2=list(pp2),protect1=list(pp1)))
    pk=[x.key() for x in pend]
    if comp[u] is not comp[v]:
        case='AC';branch('A',[a]);branch('C',[c])
    elif len(pend)==1:case='B';branch('B',pk)
    elif sb is not None and sb.key()==uk:case='RB';branch('RB',[c])
    elif sd is not None and sd.key()==uk:case='RB';branch('RB',[a])
    else:
        rbstar=False
        if len(pend)>=2 and p2[v] is lca and uncle is not None:
            shape=frozenset((pk[0],pk[1]))
            def shapeof(n):return n.key() if not n.ch else frozenset(shapeof(x) for x in n.ch)
            for k in pk[2:]:shape=frozenset((shape,k))
            rbstar=all(k in b1 for k in pk) and shapeof(uncle)==shape
        if rbstar:case='RB*';branch('RB*',[a])
        elif len(pend)==2 and uk in b2 and sibling(lca,p2) is b2[uk]:case='2B';branch('2B',pk)
        elif len(pend)>=2 and uk in b2 and b2[uk].protected and p2[b2[uk]] is pend[0]:
            case='BCY';branch('B',pk);branch('CY',[c,sibling(b2[uk],p2).key()])
        elif len(pend)==2:
            case='A2BC'
            if v.protected:branch('B',pk);branch('A',[a],pk)
            else:branch('A',[a]);branch('B',pk);branch('C',[c],[a]+pk,[a])
        else:
            assert len(pend)>=3,'trivial input';case='A3BC'
            branch('A',[a]);branch('B',pk);branch('C',[c],[a],[a])
    for b in specs:
        try:cut_batch(st.f,b['cuts']);b['legal']=True
        except AssertionError:b['legal']=False
    return dict(pair=list(pair),case=case,pendants=pk,branches=specs)

def apply(st,spec):
    assert spec['legal'],'illegal branch'
    st=deepcopy(st);by=index([st.t])[0]
    for k in spec['protect1']:by[k].protected=True
    st.f=cut_batch(st.f,spec['cuts'],spec['protect2'])
    return normalize(st)

def branch(st,pair,name):
    info=classify(st,pair);b=next(b for b in info['branches'] if b['name']==name)
    return apply(st,b),info

def check(name,observed,expected,scope='exposed calibration'):
    good=observed==expected
    records.append(dict(id=name,scope=scope,passed=good,observed=observed,expected=expected))
    assert good,(name,observed,expected)

def failed(name,fn):
    try:fn()
    except AssertionError as exc:
        records.append(dict(id=name,expected='reject',observed='reject',reason=str(exc),passed=True));return
    raise AssertionError('corruption escaped: '+name)

records=[]
def main():
    start=time.perf_counter()
    check('null-current-invocation',1+sum([]),1,'hand plant')
    st=State(parse('((a,b),c)'),[parse('((a,b),c)')]);st=normalize(st)
    check('common-cherry-contract',st.active(),2,'hand plant')
    # Batch siblings legal in the original component even if sequential recheck would reject.
    t=parse('(a,(b,c))');st=State(deepcopy(t),[t]);set_prot(st,[],['b'])
    out=cut_batch(st.f,['a','c']);check('simultaneous-batch',sorted(n.key() for n in out),['a','b','c'],'hand plant')
    st=State(parse('((a,b),c)'),[parse('((a,b),c)')]);set_prot(st,[],['a,b'])
    out=cut_batch(st.f,['a']);check('suppression-inherits',index(out)[0]['b'].protected,True,'hand plant')
    failed('protected-cut',lambda:cut_batch(out,['b']))
    # Original controls: no intermediate state is used as input.
    nine=json.loads((ROOT/'results/thesis-complexity-reachable-trace.json').read_text())
    st=State(parse(nine['trace'][0]['F1']),[parse(nine['trace'][0]['F2'])]);seq=[]
    for row in nine['trace']:
        info=classify(st,row['pair']);check('nine-case-'+str(len(seq)),info['case'],row['case'])
        check('nine-pendants-'+str(len(seq)),info['pendants'],row['pendants']);seq.append(info)
        if 'chosen_branch' in row:st=apply(st,next(b for b in info['branches'] if b['name']==row['chosen_branch']))
    C=next(b for b in info['branches'] if b['name']=='C');child=apply(st,C)
    ci=classify(child,choices(child)[0]);check('nine-dead-C',sum(b['legal'] for b in ci['branches']),0)
    mass=F(1,4)+F(1,8)+F(3,16);check('nine-mass',str(mass),'9/16');check('nine-parent',str(F(1,2)),'1/2')
    failed('known-false-mass',lambda:check('corrupted-mass',str(mass),'1/2','intentional corruption'))
    thirteen=json.loads((ROOT/'results/thesis-complexity-three-credit-trace.json').read_text())
    st=State(parse(thirteen['trace'][0]['F1']),[parse(thirteen['trace'][0]['F2'])]);P=set();Q=set();seq13=[]
    for ix,row in enumerate(thirteen['trace']):
        info=classify(st,row['pair']);check('thirteen-case-'+str(ix),info['case'],row['case']);check('thirteen-pendants-'+str(ix),info['pendants'],row['pendants'])
        check('thirteen-credits-'+str(ix),[len(P),len(Q)],row['P_Q_cardinalities']);seq13.append(info)
        if 'chosen_branch' in row:
            name=row['chosen_branch']
            if name=='C':P.add(row['pair'][0]);Q.update([row['pair'][0]] if info['case']=='A3BC' else [])
            st=apply(st,next(b for b in info['branches'] if b['name']==name))
    check('three-credit-no-cap',[len(P),len(Q)],[3,2])
    controls=json.loads((ROOT/'thesis_complexity/repair/controls-frozen.json').read_text())
    for fixture in controls['controls'][2:]:
        st=set_prot(State(parse(fixture['F1']),[parse(fixture['F2'])]),fixture['protected_F1'],fixture['protected_F2'])
        if fixture['id']=='wrong-orientation':
            failed('wrong-orientation',lambda:classify(st,fixture['chosen_pair']))
            ci=classify(st,fixture['chosen_pair'],False);child=apply(st,next(b for b in ci['branches'] if b['name']=='C'))
            check('illegal-orientation-one-pendant',len(path_info(child,'a','x')[1]),1)
        else:
            ci=classify(st,fixture['chosen_pair']);child=apply(st,next(b for b in ci['branches'] if b['name']=='C'))
            nextinfo=classify(child,choices(child)[0]);check(fixture['id']+'-C-pendants',len(nextinfo['pendants']),3)
            if fixture['id']=='live-two-leaf':check('live-C-branches',[b['name'] for b in nextinfo['branches'] if b['legal']],['B'])
    payload=dict(status='checked',scope='exposed finite calibration, not a universal theorem',elapsed_seconds=time.perf_counter()-start,records=records,nine_trace=seq,thirteen_trace=seq13,independence='fresh code; stdlib only; original source and explicit fixture data shared; no prior checker implementation imported')
    OUT.write_text(json.dumps(payload,indent=2)+'\n');print(json.dumps({k:payload[k] for k in ('status','scope','elapsed_seconds')}));print('records',len(records))
if __name__=='__main__':main()
