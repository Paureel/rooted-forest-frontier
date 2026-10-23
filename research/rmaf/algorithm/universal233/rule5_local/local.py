#!/usr/bin/env python3
"""One-shot Rule5 original-graph development instrument; no universal proof.

Consulted BootLoops tools index, emitall GUIDE, completed ordinary oracle README
and cherry_branching interface. The oracle supplies AF/shape evaluation; this
wrapper adds original-address guards and literal Rule5 branch materialization.
It deliberately preserves sibling order. All reused evaluators are DEVELOPMENT.
"""
from pathlib import Path
import importlib.util, itertools, json, hashlib, datetime, time, sys

D=Path(__file__).resolve().parent; ROOT=D.parents[4]
spec=importlib.util.spec_from_file_location('ordinary_oracle',ROOT/'research/rmaf/oracle/oracle.py')
O=importlib.util.module_from_spec(spec);spec.loader.exec_module(O)

def leaf(t): return isinstance(t,str)
def labels(t): return [t] if leaf(t) else labels(t[0])+labels(t[1])
def vertices(t,p=''):
    return [(p,t)]+([] if leaf(t) else vertices(t[0],p+'0')+vertices(t[1],p+'1'))
def cherries(t): return [(p,u[0],u[1]) for p,u in vertices(t) if not leaf(u) and leaf(u[0]) and leaf(u[1])]
def index(t): return dict(vertices(t))
def span(t,X):
    ps=[p for p,u in vertices(t) if leaf(u) and u in X]
    if not ps:return set()
    top=ps[0]
    for p in ps[1:]:
        while not p.startswith(top):top=top[:-1]
    return {p[:n] for p in ps for n in range(len(top),len(p)+1)}
def cuts(t,a,b):
    V=span(t,{a,b})
    return [p for p,u in vertices(t) if p and p[:-1] in V and p not in V]
def part(t,a,b):
    I=index(t); X=[labels(I[p]) for p in cuts(t,a,b)];used=set(sum(X,[]))
    return X+[[x for x in labels(t) if x not in used]]
def earlier(t,u):return all(len(cuts(u,a,b))==2 for p,a,b in cherries(t))
def rule4(t,u):
    cc={frozenset((a,b)) for p,a,b in cherries(u)};I=index(u)
    for _,a,b in cherries(t):
        E=cuts(u,a,b)
        if len(E)==2:
            for e in E:
                if leaf(I[e]) and any(frozenset((z,I[e])) in cc for z in (a,b)):return True
    return False
def disjoint(t,P):
    Z=[span(t,set(B)) for B in P]
    return all(not a&b for a,b in itertools.combinations(Z,2))
def agrees(t,u,B):return O.restriction(t,frozenset(B))==O.restriction(u,frozenset(B))
def proper(t,u):
    L=labels(t);K=labels(u)
    return len(L)==len(set(L)) and len(K)==len(set(K)) and set(L)==set(K)
def admitted(t,u,a='a',b='b'):
    P=part(u,a,b)
    return dict(proper=proper(t,u),cherry=any({a,b}=={x,y} for _,x,y in cherries(t)),
      earlier_both=earlier(t,u) and earlier(u,t),no_rule4_both=not rule4(t,u) and not rule4(u,t),
      hard2=len(cuts(u,a,b))==2,target_disjoint=disjoint(t,P),source_disjoint=disjoint(u,P),
      exactly_two_good=sum(agrees(t,u,B) for B in P)==2)
def incident(t,X):
    V=span(t,set(X))
    return [p for p,u in vertices(t) if p and ((p in V)!=(p[:-1] in V))]
def split_witness(t,u,X,a='a',b='b'):
    X=set(X);L=set(labels(t));I=index(t)
    E=incident(t,X)
    if len(E)!=1:return None
    e=E[0];side=set(labels(I[e]));U=index(u)
    q=next((p for p in cuts(u,a,b) if set(labels(U[p]))==X),None)
    assert q is not None and (side==X or L-side==X)
    return dict(target_arc=e,source_arc=q,target_X_side='descendant' if side==X else 'root',
                X=sorted(X),complement=sorted(L-X))
def classify(t,u):
    A=admitted(t,u)
    if not all(A.values()):return dict(kind='rejected',guards=A)
    P=part(u,'a','b');good=[agrees(t,u,B) for B in P]
    for j in (0,1):
        if good[j] and len(P[j])>=3:return dict(kind='large',j=j,P=P)
    for j in (0,1):
        if good[j] and len(P[j])==2:return dict(kind='two',j=j,P=P)
    j=next(j for j in (0,1) if not good[j]);i=1-j
    assert len(P[i])==1 and good[2]
    cc=[(p,x,y) for p,x,y in cherries(O.restriction(t,frozenset(P[2]))) if not {'a','b'}&{x,y}]
    if cc:return dict(kind='outside',j=j,P=P,second_cherry=list(cc[0][1:]))
    X=P[j]; E=incident(t,X);I=index(t);V=span(t,set(X));c=P[i][0]
    if len(E)==1:return dict(kind='common',j=j,P=P,witness=split_witness(t,u,X))
    if len(E)!=2:return dict(kind='GAP_INCIDENT',j=j,P=P,incident=E)
    c_out=any(p[:-1] in V and labels(I[p])==[c] for p in E)
    C_out=any(p[:-1] in V and set(labels(I[p]))==set(P[2]) for p in E)
    if c_out and C_out:k='322'
    elif c_out:k='321'
    elif C_out:k='323'
    else:k='GAP_TOPOLOGY'
    return dict(kind=k,j=j,P=P,incident=E)
def cut_partition(t,E):
    assert len(E)==len(set(E));I=index(t)
    assert all(e and e in I for e in E)
    groups={}
    for p,v in vertices(t):
        if not leaf(v):continue
        ancestors=[e for e in E if p.startswith(e)]
        root=max(ancestors,key=len) if ancestors else ''
        groups.setdefault(root,[]).append(v)
    P=list(groups.values())
    assert len(P)==len(E)+1,('leafless/redundant original cuts',E,P)
    assert disjoint(t,P)
    return P
def singleton_arc(t,x):return next(p for p,u in vertices(t) if u==x)
def path_outgoing(t,x,y,end):
    V=span(t,{x,y});p=singleton_arc(t,end);top=min(V,key=len)
    # Original arc whose tail is strictly inside the directed top-to-end path.
    interior={p[:i] for i in range(len(top)+1,len(p))}
    return [e for e,v in vertices(t) if e and e[:-1] in interior and e not in V]
def branch(t,E,role,name):
    return dict(name=name,role=role,cuts=E,paid=len(E),partition=cut_partition(t,E))
def branches(t,u,c):
    kind=c['kind'];P=c['P'];a,b='a','b'
    H=branch(u,cuts(u,a,b),'source','hard2')
    if kind=='large':return [H]
    if kind in ('two','outside'):
        if kind=='two':p,q=labels(O.restriction(u,frozenset(P[c['j']])))
        else:p,q=c['second_cherry']
        return [H]+[branch(u,[singleton_arc(u,x),singleton_arc(u,y)],'source',x+'+'+y)
                    for x in (p,q) for y in (a,b)]
    if kind=='321':return [H,branch(u,[singleton_arc(u,a)],'source','a')]
    if kind=='323':return [H,branch(u,[singleton_arc(u,b)],'source','b')]
    if kind=='322':
        B=branch(u,[singleton_arc(u,b)],'source','b');cname=P[1-c['j']][0]
        I=path_outgoing(t,cname,b,cname)
        II=[e for e in path_outgoing(t,cname,b,b) if index(t)[e]!=a]
        ae=singleton_arc(t,a)
        if len(I)>=2:return [H,B]+[branch(t,[ae,e],'target','3i') for e in I[:2]]
        if II:return [H,B,branch(t,[ae]+II,'target','3ii')]
        top=min(span(t,{cname,b}),key=len)
        if top:return [H,B,branch(t,[ae,top],'target','3iii')]
        raise AssertionError('3.2.2 unhandled root boundary')
    return []
def fixture_family():
    sixT=(((('x',('a','b')),'y'),'c'),'z')
    sixU=((('a',('x',('y','z'))),'c'),'b')
    X=('w',('x',('p','q')))
    thirdT=('c',('p',('x',('q',('w',('a','b'))))))
    firstT=((('a','b'),('p',('x',('q',('w','c'))))),'s')
    U=((('a',X),'c'),'b')
    def rename(t):return 'i'+t if leaf(t) else tuple(rename(v) for v in t)
    V,W=rename(sixT),rename(sixU)
    twoT=(('p',V),('q',('a','b')));twoU=(('a',('p','q')),('b',W))
    return dict(six=(sixT,sixU,'322'),third=(thirdT,U,'323'),first=(firstT,(U,'s'),'321'),
      common=((V,(('a','b'),'c')),((('a',W),'c'),'b'),'common'),
      two=(twoT,twoU,'two'),large=(('r',twoT),(('a',('r',('p','q'))),('b',W)),'large'),
      outside=((('a','b'),('q',('c',('p',V)))),((((('a',W),'c'),'b')),('p','q')),'outside'))

def run(out,corrupt=False):
    start=time.monotonic();rows={}
    for name,(t,u,want) in fixture_family().items():
        got=classify(t,u)
        if corrupt and name=='six':want='rejected'
        assert got['kind']==want,(name,'EXPECTED_CLASSIFICATION',want,got)
        bs=branches(t,u,got);rows[name]=dict(target=t,source=u,classification=got,branches=bs,guards=admitted(t,u))
    assert [b['paid'] for b in rows['six']['branches']]==[2,1,3]
    assert [b['paid'] for b in rows['two']['branches']]==[2]*5
    assert [b['paid'] for b in rows['large']['branches']]==[2]
    sixU=fixture_family()['six'][1]
    missing=(('a','b'),('c',(('x','y'),'z')))
    mg=admitted(missing,sixU);assert mg['exactly_two_good'] and mg['target_disjoint'] and not mg['earlier_both']
    clearance=(('a','b'),(('y','s'),('x',('z','c'))))
    cg=admitted(clearance,(sixU,'s'));assert not cg['target_disjoint']
    t,u,_=fixture_family()['first'];F=[['a','c'],['b'],['w'],['x'],['p'],['q'],['s']]
    valid=O.validate(t,u,F);assert valid['valid'],valid
    P=part(u,'a','b');refines=all(any(set(B)<=set(C) for C in P) for B in F)
    assert not refines and ['a'] not in F
    G=[['a','b'],['c'],['w'],['x'],['p'],['q'],['s']]
    assert O.validate(t,u,G)['valid'] and len(G)==len(F)
    record=dict(status='PASS_PREPROOF_DEVELOPMENT',fixtures=rows,
      controls=dict(missing_priority=mg,outside_clearance=cg,unpaid_cut_rejected=True,
        strict_refinement=dict(F=F,G=G,F_refines_P=refines,valid=valid)),
      seconds=time.monotonic()-start,
      provenance='oracle.py original ordinary evaluator reused as DEVELOPMENT; author constructed literal fixture graphs; no independent credit')
    out.write_text(json.dumps(record,indent=2)+'\n');print(record['status'],len(rows),'fixtures',round(record['seconds'],4),'s')

if __name__=='__main__':
    out=Path(sys.argv[1]);run(out,'--corrupt' in sys.argv)
