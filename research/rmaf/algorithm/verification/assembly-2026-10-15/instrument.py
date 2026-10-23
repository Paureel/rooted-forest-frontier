"""Prerelease assembly reference. No author or other verifier imports.

Reuses only this reviewer's explicitly disclosed, immutable pre-core graph and
pointer generator. New agreement, geometry, forest-cover and receipt code is
below. The code is a finite test instrument, never a proposed MAF algorithm.
"""
from pathlib import Path
import hashlib,importlib.util,json
from fractions import Fraction

ROOT=Path(__file__).resolve().parents[5]
OLD=ROOT/'research/rmaf/algorithm/verification/core-completion-2026-10-15/frozen-v1/independent_instrument.py'
OLD_SHA='d5cb7216e7076c9e9df4c04557855617cc041b985f78bdf15a7718b446105b9d'
assert hashlib.sha256(OLD.read_bytes()).hexdigest()==OLD_SHA
spec=importlib.util.spec_from_file_location('own_frozen_graph',OLD)
base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)

def restricted_shape(t,selected):
    """Unordered rooted label-preserving restriction, suppressing unary nodes."""
    if type(t) is int:return ('L',t) if t in selected else None
    a,b=(restricted_shape(x,selected) for x in t)
    if a is None:return b
    if b is None:return a
    return ('N',*sorted([a,b],key=repr))

def agreement(t,u,F):
    gt,gu=base.OriginalGraph(t),base.OriginalGraph(u)
    return (base.proper_partition(gt,F) and base.proper_partition(gu,F)
      and base.convex_partition(gt,F) and base.convex_partition(gu,F)
      and all(restricted_shape(t,set(p))==restricted_shape(u,set(p)) for p in F))

def parent_check(t,P):
    g=base.OriginalGraph(t)
    return len(P)==3 and base.proper_partition(g,P) and base.convex_partition(g,P)

def target_clears(t,pieces,v):
    g=base.OriginalGraph(t);v=tuple(v)
    if v not in g.at:raise ValueError('invalid original target vertex')
    return all(g.at[v] not in g.span(b) for b in pieces)

def region_from_graph(t,v,x):
    """Actual component at deletion of v, via original graph first path step.

    At non-target leaves: left child=0, right child=1, parent=2. The target
    itself has special color3, which must never be mistaken for clearance.
    """
    g=base.OriginalGraph(t);v=tuple(v)
    if v not in g.at:raise ValueError('invalid target')
    candidates=[node for node,label in g.leaf.items() if label==x]
    if len(candidates)!=1:raise ValueError('label not uniquely present')
    a=candidates[0];root=g.at[v]
    if a==root:return 3
    nxt=g.path(root,a)[1]
    if g.parent[root]==nxt:return 2
    return g.children[root].index(nxt)

def local_value(t,v,w,x,mode):
    if mode=='constant':return 0
    a=region_from_graph(t,v,x)
    if mode=='v':return a
    z=region_from_graph(t,w,x)
    if mode=='w':return z
    if mode=='joint':return 4*a+z
    raise ValueError('unknown local mode')

def tagged_colors(source,target,P,v,w,modes):
    if not parent_check(source,P):raise ValueError('not proper three-parent source partition')
    out={};counts=[]
    for i,(parent,mode) in enumerate(zip(P,modes,strict=True)):
        local={x:local_value(target,v,w,x,mode) for x in parent}
        counts.append(len(set(local.values())))
        for x,value in local.items():out[x]=3*value+i
    assert len(set(out.values()))==sum(counts)
    assert all(out[x]%3==i for i,p in enumerate(P) for x in p)
    return out,counts

def requested_clear(target,P,Q,requests,vertices):
    if not base.refines(Q,P):return False
    groups=[[b for b in Q if set(b)<=set(p)] for p in P]
    return all(target_clears(target,groups[i],vertices[name]) for i,name in requests)

def pendant_edges(t,a,b):
    g=base.OriginalGraph(t)
    endpoint={x:next(v for v,y in g.leaf.items() if y==x) for x in (a,b)}
    route=g.path(endpoint[a],endpoint[b]);on=set(route);pendants=[]
    for vertex in route:
        for neighbor in sorted(g.adj[vertex]-on):
            # A pendant original source cut must be a downward original edge.
            # This control's LCA is the original root, so no upward exception
            # is silently coerced into a rooted pendant edge.
            if g.parent[neighbor]!=vertex:raise ValueError('upward off-path edge requires explicit convention')
            pendants.append(list(g.address[neighbor]))
    return [list(g.address[v]) for v in route],pendants

def cherry(t,where,a,b):
    g=base.OriginalGraph(t);v=g.at.get(tuple(where))
    if v is None or v not in g.children:return False
    children=g.children[v]
    return all(w in g.leaf for w in children) and {g.leaf[w] for w in children}=={a,b} and a!=b

def raw_mass(outputs,c):
    c=Fraction(c)
    return sum((c**(-len(o['cuts'])) for o in outputs),Fraction(0))

def validate_output(t,colors,q,o):
    return base.validate_emission(t,colors,q,o)

def receipt(call_id,outputs):
    return {'id':call_id,'outputs':outputs,'costs':[len(o['cuts']) for o in outputs]}

def validate_receipts(rows,expected_ids):
    if not isinstance(rows,list):raise ValueError('receipt is not a raw list')
    ids=[]
    for row in rows:
        if not isinstance(row,dict) or set(row)!= {'id','outputs','costs'}:raise ValueError('receipt fields')
        if not isinstance(row['id'],str) or not isinstance(row['outputs'],list) or not isinstance(row['costs'],list):raise ValueError('receipt types')
        if len(row['costs'])!=len(row['outputs']):raise ValueError('omitted emitted cost')
        for o,cost in zip(row['outputs'],row['costs'],strict=True):
            if set(o)!={'partition','cuts'} or type(cost) is not int or cost<0 or cost!=len(o['cuts']):raise ValueError('forged emitted cost')
        ids.append(row['id'])
    if ids!=expected_ids or len(set(ids))!=len(ids):raise ValueError('omitted/duplicate/reordered literal call receipt')
    return True
