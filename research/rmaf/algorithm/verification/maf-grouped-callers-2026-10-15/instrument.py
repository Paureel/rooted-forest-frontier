"""One-shot original/grouped caller controls; never a production MAF solver.

Uses only this reviewer's immutable original graph/restriction primitives.
Finite minima are control oracles and are deliberately absent from run_caller.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction
from copy import deepcopy
import hashlib,importlib.util,sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[5]
OLD=ROOT/'research/rmaf/algorithm/verification/kept-parent-2026-10-15/instrument.py'
SPEC=importlib.util.spec_from_file_location('own_frozen_restrictions',OLD);K=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(K)
G=K.graph
restrict=K.literal_restrict
shape=K.unordered_shape
ENUMERATIONS=[]
def leaves(t):return [] if t is None else G.syntax_leaves(t)
def partition(labels,F):
    return all(F) and all([x for b in F for x in b].count(x)==1 for x in labels) and all(x in labels for b in F for x in b)
def embeddings(t,F):
    if t is None:return F==[]
    try:
        g=G.OriginalGraph(t);spans=[g.span(b) for b in F]
        return all(not spans[i]&spans[j] for i in range(len(spans)) for j in range(i))
    except (ValueError,TypeError):return False

def agreement(s,t,F):
    try:return (G.proper_partition(G.OriginalGraph(s),F) and G.proper_partition(G.OriginalGraph(t),F)
       and embeddings(s,F) and embeddings(t,F) and all(shape(restrict(s,b))==shape(restrict(t,b)) for b in F))
    except (ValueError,TypeError):return False

def partitions(xs):
    if not xs:return [[]]
    result=[]
    def walk(i,bs):
        if i==len(xs):result.append(deepcopy(bs));return
        for b in bs:
            b.append(xs[i]);walk(i+1,bs);b.pop()
        bs.append([xs[i]]);walk(i+1,bs);bs.pop()
    walk(0,[]);return result

def local_minimum(s,t):
    xs=leaves(s);assert len(xs)<=4 and len(xs)==len(set(xs)), 'control enumeration bounded to four distinct labels'
    ps=partitions(xs);valid=[F for F in ps if agreement(s,t,F)]
    assert valid;cost=min(len(F)-1 for F in valid)
    ENUMERATIONS.append({'labels':xs,'partitions':len(ps),'minimum':cost})
    return cost,[F for F in valid if len(F)-1==cost]

def pretest(s,t):
    # A tiny control implementation of exact depth0/1, not a general tool.
    for F in partitions(leaves(s)):
        if len(F)<=2 and agreement(s,t,F):return F
    return None

def original_guard(s,t,Q):
    ls,lt=leaves(s),leaves(t)
    return (len(ls)==len(set(ls)) and len(lt)==len(set(lt)) and Counter(ls)==Counter(lt)
      and partition(ls,Q) and partition(lt,Q) and embeddings(s,Q) and embeddings(t,Q))

def prepare(c):
    if not original_guard(c['source'],c['target'],c['Q']):return None
    slots=[]
    for j,U in enumerate(c['Q']):
        s,t=restrict(c['source'],U),restrict(c['target'],U)
        assert s is not None and t is not None and Counter(leaves(s))==Counter(U)==Counter(leaves(t))
        F=pretest(s,t)
        slots.append({'slot':j,'id':c['slot_ids'][j],'source':s,'target':t,'U':U,
                      'stored':F,'lower':len(F)-1 if F is not None else 2})
    return slots

def run_caller(c):
    """Public pretest/lower bounds only. Does not call local_minimum."""
    slots=prepare(c);trace=[]
    if slots is None:return {'slots':None,'trace':trace,'forest':None,'reason':'premise-guard'}
    lower=sum(x['lower'] for x in slots)
    if lower>c['q']:return {'slots':slots,'trace':trace,'forest':None,'reason':'public-lower-over-budget'}
    solved=[]
    for slot in slots:
        j=slot['slot']
        if slot['stored'] is not None:solved.append(slot['stored']);continue
        budget=c['q']-(lower-slot['lower'])
        trace.append({'slot':j,'id':slot['id'],'budget':budget})
        if c.get('fail_slot')==j:return {'slots':slots,'trace':trace,'forest':None,'reason':'first-recursive-failure'}
        F=deepcopy(c['witnesses'][j])
        if not agreement(slot['source'],slot['target'],F) or len(F)-1>budget:
            return {'slots':slots,'trace':trace,'forest':None,'reason':'invalid-local-return'}
        solved.append(F)
    forest=[b for F in solved for b in F]
    add=len(forest)-len(c['Q'])
    if add>c['q']:return {'slots':slots,'trace':trace,'forest':None,'reason':'joint-over-budget','returned_cost':add}
    assert add>=0
    return {'slots':slots,'trace':trace,'forest':forest,'additional':add,'original_cuts':len(forest)-1,'reason':'success'}

def normalized_mass(trace,q,base):
    base=Fraction(base);return sum((base**(r['budget']-q) for r in trace),Fraction(0))
def family(U,F):return [b for b in F if set(b)<=set(U)]
def proper_state(T,ss):
    labels=leaves(T)
    return len(labels)==len(set(labels)) and partition(labels,[leaves(s) for s in ss])
def state_agrees(T,ss,F):
    labels=leaves(T)
    if not proper_state(T,ss) or not partition(labels,F) or not embeddings(T,F):return False
    if not all(any(set(b)<=set(leaves(s)) for s in ss) for b in F):return False
    for s in ss:
        local=family(leaves(s),F)
        if not partition(leaves(s),local) or not embeddings(s,local):return False
        if not all(T is not None and shape(restrict(T,b))==shape(restrict(s,b)) for b in local):return False
    return True

def grouped(T,ss,Q,F):
    owners=[]
    for s in ss:
        opts=[j for j,U in enumerate(Q) if set(leaves(s))<=set(U)]
        owners.append(opts[0] if len(opts)==1 else None)
    ownership=all(x is not None for x in owners)
    cross=True;within=False
    if T is not None:
        g=G.OriginalGraph(T)
        for i in range(len(ss)):
            for j in range(i):
                if owners[i] is None or owners[j] is None:cross=False;continue
                overlap=bool(g.span(leaves(ss[i]))&g.span(leaves(ss[j])))
                if owners[i]!=owners[j] and overlap:cross=False
                if owners[i]==owners[j] and overlap:within=True
    local=[]
    for j,U in enumerate(Q):
        indices=[i for i in range(len(ss)) if set(leaves(ss[i]))<=set(U)]
        owned=[ss[i] for i in indices];target=restrict(T,U) if T is not None else None;blocks=family(U,F)
        local.append({'indices':indices,'sources':owned,'target':target,'forest':blocks,'agrees':state_agrees(target,owned,blocks),'cost':max(0,len(blocks)-len(owned)),'integer_cost':len(blocks)-len(owned)})
    return {'proper':proper_state(T,ss),'checked_Q':partition(leaves(T),Q),'owners':owners,'ownership':ownership,
            'cross':cross,'within':within,'whole_group_disjoint':embeddings(T,Q),'global_agrees':state_agrees(T,ss,F),
            'local':local,'additional':max(0,len(F)-len(ss)),'integer_additional':len(F)-len(ss)}

def child_query(E,q,contract):
    if q==0:return {'budget':None,'forest':None,'reason':'q-positive-required'}
    if contract is None:return {'budget':None,'forest':None,'reason':'missing-child-contract'}
    if contract.get('target')!=E['target'] or contract.get('sources')!=E['sources'] or contract.get('kind')!='ResidualFeasibility':
        return {'budget':None,'forest':None,'reason':'wrong-child-contract'}
    budget=q-1
    F=None if budget==0 else ([[3],[5],[4,6]] if budget==1 else [[3],[4],[5],[6]])
    if F is not None:
        assert state_agrees(E['target'],E['sources'],F) and 0<=len(F)-len(E['sources'])<=budget
    return {'budget':budget,'forest':F,'reason':'actual-child-result'}
