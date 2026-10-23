#!/usr/bin/env python3
"""One-campaign independent bridge verifier; no campaign oracle imports.
See GUIDE.md for scope, controls, and provenance. Stdlib and exact integers only.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, time
from collections import deque
from functools import lru_cache
from pathlib import Path

class Tree:
    def __init__(self, shape):
        self.shape = shape
        self.adj = {}
        self.labels = {}
        self.children = {}
        def walk(t, v=()):
            self.adj[v] = set()
            if isinstance(t, str):
                if t in self.labels: raise ValueError('duplicate leaf')
                self.labels[t] = v
            else:
                if len(t) != 2: raise ValueError('not binary')
                self.children[v] = (v+(0,),v+(1,))
                for i,s in enumerate(t):
                    u = v+(i,)
                    walk(s,u)
                    self.adj[v].add(u); self.adj[u].add(v)
        walk(shape)
    def path(self,a,b):
        prev={a:None}; q=deque([a])
        while q:
            x=q.popleft()
            if x==b: break
            for y in self.adj[x]:
                if y not in prev: prev[y]=x; q.append(y)
        result={b}
        while b != a: b=prev[b]; result.add(b)
        return frozenset(result)
    @lru_cache(None)
    def hull(self, labels):
        labels = frozenset(labels)
        if not labels: return frozenset()
        vs=[self.labels[x] for x in sorted(labels)]
        ans=set(vs)
        for v in vs[1:]: ans.update(self.path(vs[0],v))
        return frozenset(ans)
    @lru_cache(None)
    def restriction(self, labels):
        def rec(t):
            if isinstance(t,str): return t if t in labels else None
            ch=[x for s in t if (x:=rec(s)) is not None]
            if len(ch)==0: return None
            if len(ch)==1: return ch[0]
            return tuple(sorted(ch,key=repr))
        return rec(self.shape)
    def root(self,labels): return min(self.hull(frozenset(labels)),key=len)
    def degree(self,labels,v): return len(self.adj[v] & self.hull(frozenset(labels)))
    def regions(self, marks):
        unseen=set(self.adj)-set(marks); regions=[]; empty=0
        while unseen:
            start=next(iter(unseen)); seen={start}; q=[start]; unseen.remove(start)
            while q:
                x=q.pop()
                for y in self.adj[x] & unseen: unseen.remove(y); seen.add(y); q.append(y)
            ls=frozenset(x for x,v in self.labels.items() if v in seen)
            if ls: regions.append(ls)
            else: empty+=1
        return tuple(regions),empty

def canon_partition(p): return tuple(sorted((frozenset(x) for x in p),key=lambda x:tuple(sorted(x))))
@lru_cache(None)
def partitions(labels):
    labels=tuple(labels)
    if not labels: return ((),)
    first,*rest=labels; ans=[]
    for p in partitions(tuple(rest)):
        ans.append(canon_partition(({first},)+p))
        for i,b in enumerate(p): ans.append(canon_partition(p[:i]+(b|{first},)+p[i+1:]))
    return tuple(ans)

def partition_ok(labels,p):
    return all(p) and len(set().union(*p))==sum(map(len,p)) and set().union(*p)==set(labels)

def local_valid(s,t,labels,p,marks=()):
    if not partition_ok(labels,p): return False
    used_s=set(); used_t=set()
    for b in p:
        if s.restriction(b)!=t.restriction(b): return False
        hs=s.hull(b); ht=t.hull(b)
        if hs & used_s or ht & used_t or ht & set(marks): return False
        used_s.update(hs); used_t.update(ht)
    return True

def optimum(s,t,labels,marks=()):
    good=[p for p in partitions(tuple(sorted(labels))) if local_valid(s,t,labels,p,marks)]
    if not good: return None,None
    p=min(good,key=len); return len(p)-1,p

def pure(t,partition):
    if not partition_ok(t.labels,partition): return False
    return all(t.degree(a,v)==t.degree(b,v)==2 for a,b in itertools.combinations(partition,2)
               for v in t.hull(a)&t.hull(b))

def all_trees(labels):
    labels=tuple(sorted(labels))
    if len(labels)==1: yield labels[0]; return
    # Every unordered root split is represented by the side containing first.
    first=labels[0]; tail=labels[1:]
    for size in range(len(tail)):
        for selected in itertools.combinations(tail,size):
            left=(first,)+selected; right=tuple(x for x in tail if x not in selected)
            for a in all_trees(left):
                for b in all_trees(right): yield (a,b)

def control_run():
    rows=[]; caught=[]
    def check(name,got,expected):
        assert got==expected,(name,got,expected)
        rows.append({'name':name,'observed':got,'expected':expected})
        if isinstance(expected,int):
            try: assert got==expected+1
            except AssertionError: caught.append(name+'-wrong-integer')
            else: raise AssertionError('fault survived')
    t=Tree('a'); check('singleton-hull',len(t.hull(frozenset('a'))),1)
    check('singleton-optimum',optimum(t,t,'a')[0],0)
    t=Tree(('a','b')); check('root-mark-cost',optimum(t,t,'ab',[()])[0],1)
    check('root-mark-regions',len(t.regions([()])[0]),2)
    t=Tree((('a','b'),('c','d'))); a=frozenset('ac'); b=frozenset('bd')
    check('cross-hull-intersection',len(t.hull(a)&t.hull(b)),3)
    check('cross-pure',pure(t,(a,b)),True)
    check('root-split-disjoint',not(t.hull(a)&(t.hull(frozenset('b'))|t.hull(frozenset('d')))),True)
    # A deliberately suppressed hull loses both internal path vertices.
    assert (t.hull(a)&t.hull(b)) != {()}; caught.append('suppressed-path-vertices')
    t3=Tree(((('a','b'),'c'),('d','e')))
    check('degree-three-purity-rejected',pure(t3,(frozenset('acd'),frozenset('be'))),False)
    check('overlapping-labels-rejected',partition_ok('abcd',(frozenset('acd'),frozenset('bd'))),False)
    t=Tree(((('a','b'),'c'),'d'))
    check('adjacent-marks-regions',len(t.regions([(),(0,)])[0]),3)
    check('adjacent-marks-optimum',optimum(t,t,'abcd',[(),(0,)])[0],2)
    t=Tree((('a','b'),('c','d'))); marks=[(0,),(1,)]
    check('empty-region-nonempty-count',len(t.regions(marks)[0]),4)
    check('empty-region-empty-count',t.regions(marks)[1],1)
    check('empty-region-optimum',optimum(t,t,'abcd',marks)[0],3)
    assert len(t.regions(marks)[0])+t.regions(marks)[1]!=4; caught.append('leafless-regions-counted')
    check('old-mark-violation-rejected',local_valid(Tree(('b','d')),t,'bd',(frozenset('bd'),),[(0,)]),False)
    s=Tree((('a','b'),'c')); t=Tree((('a','c'),'b'))
    check('triplet-disagreement',optimum(s,t,'abc')[0],1)
    t=Tree(((('a','b'),'c'),(('d','e'),'f')))
    p=tuple(frozenset(x) for x in ('ad','be','cf'))
    check('three-clique-purity',pure(t,p),True)
    best=10
    for refinements in itertools.product(*(partitions(tuple(sorted(b))) for b in p)):
        blocks=tuple(x for q in refinements for x in q)
        if all(not(t.hull(a)&t.hull(b)) for a,b in itertools.combinations(blocks,2)):
            best=min(best,len(blocks)-3)
    check('three-clique-cost',best,2)
    # Candidate's finite mark-interaction case; read only after frozen controls.
    s=Tree((('0','2'),'1')); t=Tree((('0','3'),('1',('2','4'))))
    four=[optimum(s,t,'012',m)[0] for m in ([],[(0,)],[(1,1)],[(0,),(1,1)])]
    assert four==[1,1,1,2]
    return {'controls':rows,'control_count':len(rows),'caught_plants':caught,
            'mark_interaction':four,'mark_interaction_status':'post-freeze candidate reproduction; not a planted control'}

def geometry_run(max_n):
    counts={'trees':0,'partitions':0,'pure_partitions':0,'deepest_neighbors':0,'free_subblocks':0,
            'degree_two_splits':0,'old_mark_sets':0,'hull_regions':0}
    for n in range(1,max_n+1):
        labels=tuple(chr(97+i) for i in range(n))
        for shape in all_trees(labels):
            t=Tree(shape); counts['trees']+=1
            for p in partitions(labels):
                counts['partitions']+=1
                if not pure(t,p): continue
                counts['pure_partitions']+=1
                maxdepth=max(len(t.root(a)) for a in p)
                for a in p:
                    if len(t.root(a))!=maxdepth: continue
                    v=t.root(a)
                    for b in p:
                        if a==b or not(t.hull(a)&t.hull(b)): continue
                        assert v in t.hull(b); counts['deepest_neighbors']+=1
                        for side,other in ((a,b),(b,a)):
                            for q in partitions(tuple(sorted(side))):
                                for block in q:
                                    if v not in t.hull(block):
                                        assert not(t.hull(block)&t.hull(other)),(shape,p,a,b,v,block)
                                        counts['free_subblocks']+=1
            for size in range(1,n+1):
                for selected in itertools.combinations(labels,size):
                    a=frozenset(selected); hull=t.hull(a)
                    for v in hull-set(t.labels.values()):
                        if t.degree(a,v)!=2: continue
                        # All valid old marks lie outside this already-feasible piece.
                        regions,_=t.regions([v])
                        blocks=tuple(r&a for r in regions if r&a)
                        assert len(blocks)==2,(shape,a,v,blocks)
                        assert all(v not in t.hull(b) and t.hull(b)<=hull for b in blocks)
                        assert not(t.hull(blocks[0])&t.hull(blocks[1]))
                        counts['degree_two_splits']+=1
                        old=set(t.adj)-set(hull)-set(t.labels.values())
                        assert all(not(t.hull(b)&old) for b in blocks)
                        counts['old_mark_sets']+=1
            internal=tuple(t.children)
            for bits in itertools.product((0,1),repeat=len(internal)):
                marks={v for v,b in zip(internal,bits) if b}
                regions,empty=t.regions(marks)
                for block in (b for p in partitions(labels) for b in p):
                    avoids=not(t.hull(block)&marks)
                    contained=any(block<=r for r in regions)
                    assert avoids==contained,(shape,marks,block)
                    counts['hull_regions']+=1
    return counts

def main():
    p=argparse.ArgumentParser(); p.add_argument('--max-n',type=int,default=3); p.add_argument('--output',required=True)
    a=p.parse_args(); started=time.time(); controls=control_run(); pilot=time.time()
    result={'schema_version':1,'status':'finite-no-fire','controls':controls,'counts':geometry_run(a.max_n),
            'max_n':a.max_n,'control_seconds':pilot-started,'elapsed_seconds':time.time()-started,
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'independence':'New BFS paths + leaf partitions; no campaign imports. Shared abstract definitions and candidate statement; candidate finite mark example was read before reproduction.'}
    Path(a.output).write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result))
if __name__=='__main__': main()
