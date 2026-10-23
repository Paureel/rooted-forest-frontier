"""One-shot kept-parent preparation wrapper; no candidate imports.

Reuses this reviewer's immutable BFS original graph / pointer generator by SHA.
The preservation, restriction, certificate and literal receipt predicates are
new here. It emits no lifted whole-source edge or budget discount.
"""
from pathlib import Path
from collections import Counter
from copy import deepcopy
import hashlib, importlib.util, sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[5]
BASE = ROOT/'research/rmaf/algorithm/verification/core-completion-2026-10-15/frozen-v1/independent_instrument.py'
BASE_SHA = 'd5cb7216e7076c9e9df4c04557855617cc041b985f78bdf15a7718b446105b9d'
assert hashlib.sha256(BASE.read_bytes()).hexdigest() == BASE_SHA
spec = importlib.util.spec_from_file_location('kept_parent_frozen_graph', BASE)
graph = importlib.util.module_from_spec(spec); spec.loader.exec_module(graph)

def source_valid(tree, parents):
    try:
        return len(parents)==3 and graph.convex_partition(graph.OriginalGraph(tree), parents)
    except (ValueError,TypeError):
        return False

def source_colors(tree, parents, beta):
    A,B,C = parents
    result = {}
    for x in graph.syntax_leaves(tree):
        if x in A: result[x] = 0
        elif x in B:
            b=beta[str(x)]
            if type(b) is not int or b<0: raise ValueError('Nat beta required')
            result[x] = 3*b+1
        elif x in C: result[x] = 2
        else: raise ValueError('source partition does not cover original label')
    return result

def whole_membership(tree, parents, blocks):
    """Order-insensitive original label MULTISET membership, computed afresh."""
    try:
        if len(parents)!=3 or not graph.proper_partition(graph.OriginalGraph(tree), blocks): return False
        A,B,C=parents
        ia=[i for i,b in enumerate(blocks) if Counter(b)==Counter(A)]
        ic=[i for i,b in enumerate(blocks) if Counter(b)==Counter(C)]
        return len(ia)==len(ic)==1 and ia[0]!=ic[0] and all(
            i in (ia[0],ic[0]) or (b and set(b)<=set(B)) for i,b in enumerate(blocks))
    except (ValueError,TypeError):
        return False

def literal_restrict(tree, labels):
    """Original ordered restriction with unary suppression, no generator state."""
    if type(tree) is int: return tree if tree in labels else None
    a,b=(literal_restrict(child,labels) for child in tree)
    if a is None: return b
    if b is None: return a
    return [a,b]

def unordered_shape(tree):
    if tree is None: return None
    if type(tree) is int: return ('leaf',tree)
    return ('node',*sorted((unordered_shape(t) for t in tree), key=repr))

def unchanged_restrictions(tree, parents, blocks):
    if not whole_membership(tree,parents,blocks): return False
    return all(literal_restrict(tree,next(b for b in blocks if Counter(b)==Counter(p)))==literal_restrict(tree,p)
               for p in (parents[0],parents[2]))

def local_certificate_valid(tree, target, parents, blocks, certificate):
    """Transport supplied LOCAL restricted-tree certificate; no global lifting."""
    try:
        if not unchanged_restrictions(tree,parents,blocks): return False
        index={'A':0,'C':2}[certificate['parent']]
        p=parents[index]; actual=next(b for b in blocks if Counter(b)==Counter(p))
        s=literal_restrict(tree,p); t=literal_restrict(target,p)
        if s!=certificate['source_restriction'] or t!=certificate['target_restriction']: return False
        if literal_restrict(tree,actual)!=s or literal_restrict(target,actual)!=t: return False
        if (unordered_shape(s)!=unordered_shape(t))!=certificate['nonhomeomorphic']: return False
        F=certificate['partition']; cost=certificate['cost']
        if cost!=1 or len(F)!=cost+1: return False
        for local,cuts in ((s,certificate['source_local_cuts']),(t,certificate['target_local_cuts'])):
            g=graph.OriginalGraph(local); r=g.residual(cuts)
            if len(cuts)!=cost or not r['nonempty'] or not r['cuts_plus_one']: return False
            if r['leaf_partition']!=graph.canonical(F) or not graph.convex_partition(g,F): return False
        return all(unordered_shape(literal_restrict(s,b))==unordered_shape(literal_restrict(t,b)) for b in F)
    except (KeyError,ValueError,TypeError,StopIteration):
        return False

def exact_rows(expected, actual):
    """Literal raw output occurrences matter; keyed row duplication is invalid."""
    if not isinstance(actual,list): return False
    try:
        ids=[(x['id'],x['q']) for x in actual]
        return len(ids)==len(set(ids)) and actual==expected
    except (KeyError,TypeError):
        return False

def exact_origins(expected, actual):
    try:
        names=[x['name'] for x in actual]
        return len(names)==len(set(names)) and sorted(expected,key=lambda x:x['name'])==sorted(actual,key=lambda x:x['name'])
    except (KeyError,TypeError):
        return False
