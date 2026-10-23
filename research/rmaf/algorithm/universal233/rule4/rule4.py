#!/usr/bin/env python3
"""Problem-specific Rule4 original-edge selector and conditional child runner.

The toolkit index, emitall guide and existing rooted-MAF oracle were consulted.
No toolkit package supplies these original-edge states. This module adds only
Rule4 logic; its optional small controls reuse the oracle, not a broad census.
The universal graph proof is in PROOF.md; author controls are not certification.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import deque
from fractions import Fraction
from typing import Callable

Tree = str | tuple['Tree', 'Tree']
Forest = tuple[tuple[str, ...], ...]


def tree(raw) -> Tree:
    seen = set()
    def rec(t):
        if isinstance(t, str) and t:
            if t in seen: raise ValueError('duplicate-label')
            seen.add(t)
            return t
        if not isinstance(t, (list, tuple)) or len(t) != 2:
            raise ValueError('nonbinary-tree')
        return (rec(t[0]), rec(t[1]))
    return rec(raw)


def canonical(t):
    if t is None or isinstance(t, str): return t
    return tuple(sorted((canonical(t[0]), canonical(t[1])), key=repr))


def leaves(t):
    return (t,) if isinstance(t, str) else leaves(t[0]) + leaves(t[1])


def restrict(t, B):
    if isinstance(t, str): return t if t in B else None
    l, r = restrict(t[0], B), restrict(t[1], B)
    if l is None: return r
    if r is None: return l
    return l, r


def forest(F) -> Forest:
    F = tuple(tuple(sorted(B)) for B in F)
    if any(not B for B in F): raise ValueError('empty-block')
    flat = tuple(x for B in F for x in B)
    if len(set(flat)) != len(flat): raise ValueError('duplicate-forest-label')
    return tuple(sorted(F))


class Graph:
    """Original vertices include every unsuppressed degree-two path vertex."""
    def __init__(self, t):
        self.tree = t
        self.subtrees, self.paths = {}, {}
        def walk(u, p):
            self.subtrees[p] = u
            if isinstance(u, str): self.paths[u] = p
            else:
                walk(u[0], p+'0'); walk(u[1], p+'1')
        walk(t, '')
        self.labels = frozenset(self.paths)
        if len(leaves(t)) != len(self.labels): raise ValueError('duplicate-label')

    def embedding(self, B):
        B = tuple(B)
        if not B or not set(B) <= self.labels: raise ValueError('bad-embedding-labels')
        pp = [self.paths[x] for x in B]
        root = pp[0]
        for p in pp[1:]:
            while not p.startswith(root): root = root[:-1]
        return frozenset(p[:i] for p in pp for i in range(len(root),len(p)+1))

    def pendant(self, a, b):
        P = self.embedding((a,b))
        return tuple(p for p in self.subtrees if p and p[:-1] in P and p not in P)

    def cherries(self):
        return tuple((p,u[0],u[1]) for p,u in self.subtrees.items()
                     if not isinstance(u,str) and isinstance(u[0],str) and isinstance(u[1],str))

    def cut_regions(self, cuts):
        if len(set(cuts)) != len(cuts): raise ValueError('duplicate-cut')
        if '' in cuts: raise ValueError('root-cut')
        if any(p not in self.subtrees for p in cuts): raise ValueError('invalid-cut')
        adj = {v:[] for v in self.subtrees}
        for v in self.subtrees:
            if v and v not in cuts:
                adj[v].append(v[:-1]); adj[v[:-1]].append(v)
        regions, seen = [], set()
        # Cuts are literal original heads. Each starts its child component.
        for root in (*cuts, ''):
            if root in seen: raise ValueError('redundant-component-root')
            todo, part = [root], set()
            while todo:
                v = todo.pop()
                if v in part: continue
                part.add(v); todo.extend(adj[v])
            seen |= part
            B = tuple(sorted(x for x,p in self.paths.items() if p in part))
            regions.append({'root':root, 'vertices':tuple(sorted(part)), 'labels':B})
        if seen != set(self.subtrees): raise ValueError('missing-original-vertices')
        if len(regions) != len(cuts)+1: raise ValueError('component-count')
        return tuple(regions)

    def partition_after(self, cuts):
        rr = self.cut_regions(cuts)
        if any(not r['labels'] for r in rr): raise ValueError('leafless-component')
        return tuple(r['labels'] for r in rr)


def refines(F, Q):
    return all(any(set(B) <= set(C) for C in Q) for B in F)


def agreement(T, S, F):
    try: F = forest(F)
    except ValueError: return False
    gt, gs = Graph(T), Graph(S)
    flat = frozenset(x for B in F for x in B)
    if flat != gt.labels or flat != gs.labels: return False
    if any(canonical(restrict(T,B)) != canonical(restrict(S,B)) for B in F): return False
    for g in (gt,gs):
        occupied = set()
        for B in F:
            V = g.embedding(B)
            if occupied & V: return False
            occupied |= V
    return True


@dataclass(frozen=True)
class Branch:
    name: str
    target: Tree
    source: Tree
    cuts: tuple[str, ...]
    partition: Forest
    source_forest: tuple[Tree, ...]
    swapped: bool

    @property
    def cost(self): return len(self.cuts)

    def check(self):
        g = Graph(self.source)
        if self.partition != g.partition_after(self.cuts): raise ValueError('wrong-literal-partition')
        if len(self.partition) != self.cost+1: raise ValueError('unpaid-cut')
        if self.source_forest != tuple(restrict(self.source,B) for B in self.partition):
            raise ValueError('wrong-source-forest')
        if any(t is None for t in self.source_forest): raise ValueError('missing-source-component')
        return True


@dataclass(frozen=True)
class Selection:
    T: Tree
    S: Tree
    a: str
    b: str
    c: str
    c_head: str
    X2_head: str
    X2: frozenset[str]
    branches: tuple[Branch, ...]


def no_common_and_no_t1(T,S):
    gt,gs=Graph(T),Graph(S)
    if gt.labels != gs.labels: return False
    ct={frozenset((a,b)) for _,a,b in gt.cherries()}
    cs={frozenset((a,b)) for _,a,b in gs.cherries()}
    if ct & cs: return False
    # The two-tree source rule permits both roles. This is the actual no-t1
    # guard needed when the third branch swaps target and cut source.
    return all(len(g.pendant(a,b)) != 1 for cherries,g in
               ((gt.cherries(),gs),(gs.cherries(),gt)) for _,a,b in cherries)


def candidates(T,S):
    gt,gs=Graph(T),Graph(S)
    if not no_common_and_no_t1(T,S): return ()
    out=[]
    def branch(name,target,source,cuts,swapped):
        Q=Graph(source).partition_after(cuts)
        b=Branch(name,target,source,tuple(cuts),Q,tuple(restrict(source,B) for B in Q),swapped)
        b.check()
        return b
    for _,u,v in gt.cherries():
        for a,b in ((u,v),(v,u)):
            pe=gs.pendant(a,b)
            if len(pe)!=2: continue
            for p,x,y in gs.cherries():
                if a not in (x,y): continue
                c = y if x==a else x
                ch = gs.paths[c]
                if ch not in pe: continue
                other=next(q for q in pe if q!=ch)
                X2=frozenset(leaves(gs.subtrees[other]))
                # c is the side group incident to a's original cherry parent.
                if gs.paths[a][:-1] != ch[:-1]: continue
                swappedcuts=gt.pendant(a,c)
                if len(swappedcuts)<2: raise AssertionError('no-t1-guard-failed')
                bb=(branch('pendants',T,S,(ch,other),False),
                    branch('isolate-a',T,S,(gs.paths[a],),False),
                    branch('swap-ac-pendants',S,T,swappedcuts,True))
                out.append(Selection(T,S,a,b,c,ch,other,X2,bb))
    return tuple(sorted(out,key=lambda s:(s.a,s.b,s.c)))


def select(T,S):
    ss=candidates(T,S)
    return ss[0] if ss else None


def covering_exchange(s: Selection,F):
    """Construct, then check a no-larger cover. No claimed safety input field.

    This function checks the derived output on the literal original trees. Its
    universal success theorem is distinct from these checks; see PROOF.md.
    """
    F=forest(F)
    if not agreement(s.T,s.S,F): raise ValueError('not-original-agreement')
    for i,b in enumerate(s.branches):
        if refines(F,b.partition): return i,F,'already-refines'
    B=next(B for B in F if s.a in B)
    D=tuple(x for x in B if x in s.X2)
    E=tuple(sorted((*[x for x in B if x not in s.X2],s.b)))
    if not D or s.c in B or (s.b,) not in F:
        raise AssertionError('first-gap:case-disjunction')
    G=forest([C for C in F if C!=B and C!=(s.b,)]+[D,E])
    if len(G)>len(F): raise AssertionError('first-gap:component-count')
    if not agreement(s.T,s.S,G): raise AssertionError('first-gap:global-exchange')
    if not refines(G,s.branches[0].partition): raise AssertionError('first-gap:source-refinement')
    return 0,G,'split-X2-and-reattach-b'


def paid_mass(s,c):
    c=Fraction(c)
    if c<2: raise ValueError('base-below-two')
    actual=sum((c**(-b.cost) for b in s.branches),Fraction())
    bound=c**(-1)+2*c**(-2)
    if actual>bound: raise AssertionError('mass-bound')
    return actual,bound


def recover_original_cuts(S,F):
    """One whole-source region extension; never union local child cut sets."""
    g=Graph(S); F=forest(F)
    occupied={}
    for i,B in enumerate(F):
        for v in g.embedding(B):
            if v in occupied: raise ValueError('source-embedding-overlap')
            occupied[v]=i
    adj={v:[] for v in g.subtrees}
    for v in g.subtrees:
        if v:
            adj[v].append(v[:-1]);adj[v[:-1]].append(v)
    todo=deque(sorted(occupied,key=lambda v:(occupied[v],v)))
    while todo:
        v=todo.popleft()
        for w in sorted(adj[v]):
            if w not in occupied: occupied[w]=occupied[v];todo.append(w)
    cuts=tuple(v for v in g.subtrees if v and occupied[v]!=occupied[v[:-1]])
    if len(cuts)!=len(F)-1: raise AssertionError('nonexact-final-cut-count')
    if forest(g.partition_after(cuts))!=F: raise AssertionError('final-cut-realization')
    return cuts


def solve_selected(s: Selection,q: int,child: Callable):
    """Under the printed exact child solver IH, return a minimum original AF.

    child(branch, residual_budget) returns None iff no agreement of branch.target
    and literal branch.source_forest can be obtained using at most that many
    additional cuts; otherwise returns a minimum component-count such agreement.
    The contract is child-specific, including the actual role swap and Q.
    This caller checks every returned original partition and reconstructs once.
    """
    if not isinstance(q,int) or q<0: raise ValueError('negative-budget')
    outputs=[];calls=[]
    for b in s.branches:
        b.check()
        if b.cost>q: continue
        residual=q-b.cost
        if not residual<q: raise AssertionError('nondecreasing-recursion')
        F=child(b,residual)
        calls.append({'branch':b.name,'cost':b.cost,'child_budget':residual,'swapped':b.swapped})
        if F is None: continue
        F=forest(F)
        if not agreement(b.target,b.source,F): raise ValueError('child-not-original-agreement')
        if not refines(F,b.partition): raise ValueError('child-not-source-refinement')
        additional=len(F)-len(b.partition)
        if additional<0 or additional>residual: raise ValueError('child-over-budget')
        if not agreement(s.T,s.S,F): raise ValueError('bad-role-swap-reconstruction')
        if len(F)-1!=b.cost+additional: raise AssertionError('cost-identity')
        outputs.append(F)
    if not outputs: return None,calls
    answer=min(outputs,key=lambda F:(len(F),F))
    cuts=recover_original_cuts(s.S,answer)
    return {'forest':answer,'k':len(answer),'q':len(cuts),'original_source_cuts':cuts},calls
