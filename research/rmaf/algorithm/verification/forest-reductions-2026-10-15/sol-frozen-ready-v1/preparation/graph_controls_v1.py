#!/usr/bin/env python3
"""One-shot independent reviewer controls, not a general toolkit engine.
Original addressed-graph paths and induced rooted topology, no checker reuse.
"""
import argparse, collections, datetime, hashlib, itertools, json, pathlib, time
HERE = pathlib.Path(__file__).resolve().parent

class Graph:
    def __init__(self, tree):
        self.child, self.taxon, self.parent = {}, {}, {}
        def visit(t, v=()):
            if t is None: return
            if isinstance(t, int): self.taxon[v] = t; self.child[v] = []
            else:
                self.child[v] = [v+(0,), v+(1,)]
                for k, x in enumerate(t):
                    self.parent[v+(k,)] = v
                    visit(x, v+(k,))
        visit(tree)
    def labels(self): return [self.taxon[v] for v in sorted(self.taxon)]
    def selected(self, B): return [v for v, x in self.taxon.items() if x in B]
    def hull(self, B):
        vs = self.selected(B)
        if not vs: return set()
        root = vs[0]
        for v in vs[1:]:
            n = 0
            while n < min(len(root), len(v)) and root[n] == v[n]: n += 1
            root = root[:n]
        return {v[:n] for v in vs for n in range(len(root), len(v)+1)}
    def restriction(self, B):
        hull = self.hull(B)
        if not hull: return None
        root = min(hull, key=len)
        def emit(v):
            cs = [c for c in self.child[v] if c in hull]
            if not cs: return self.taxon[v]
            if len(cs) == 1: return emit(cs[0])
            return [emit(c) for c in cs]
        return emit(root)
    def cherry_parent(self, a, b):
        if a == b: return None
        va = [v for v, x in self.taxon.items() if x == a]
        vb = [v for v, x in self.taxon.items() if x == b]
        if len(va) != 1 or len(vb) != 1: return None
        if va[0] and va[0][:-1] == vb[0][:-1]: return va[0][:-1]
        return None
    def contracted(self, a, b, z):
        p = self.cherry_parent(a,b)
        def emit(v):
            if v == p: return z
            if v in self.taxon: return self.taxon[v]
            return [emit(c) for c in self.child[v]]
        return None if not self.child else emit(())

def canonical(t):
    if t is None: return ('empty',)
    if isinstance(t,int): return ('leaf',t)
    return ('node',)+tuple(sorted((canonical(x) for x in t), key=repr))
def labels(t): return Graph(t).labels()
def partition(X,F):
    flat = [x for B in F for x in B]
    return all(B for B in F) and collections.Counter(flat) == collections.Counter(X)
def proper(T,ss):
    X=labels(T)
    return len(X)==len(set(X)) and partition(X,[labels(s) for s in ss])
def disjoint(T,F):
    hs=[Graph(T).hull(B) for B in F]
    return all(not hs[i] & hs[j] for i in range(len(hs)) for j in range(i))
def agrees(T,ss,F):
    if not proper(T,ss) or not partition(labels(T),F): return False
    sets=[set(labels(s)) for s in ss]
    if not all(any(set(B)<=S for S in sets) for B in F): return False
    if not disjoint(T,F): return False
    for s,S in zip(ss,sets):
        G=[B for B in F if set(B)<=S]
        if not partition(labels(s),G) or not disjoint(s,G): return False
        for B in G:
            if canonical(Graph(T).restriction(B)) != canonical(Graph(s).restriction(B)): return False
    return True

def partitions(X):
    if not X: yield []; return
    head,*tail=X
    for F in partitions(tail):
        yield [[head]]+[list(B) for B in F]
        for j in range(len(F)):
            G=[list(B) for B in F]; G[j]=[head]+G[j]; yield G

def forests(T,ss):
    if not proper(T,ss): return []
    return [F for F in partitions(labels(T)) if agrees(T,ss,F)]
def cost(ss,F): return max(0,len(F)-len(ss))
def ready(T,ss,a,b,z):
    return proper(T,ss) and a!=b and z not in labels(T) and Graph(T).cherry_parent(a,b) is not None and any(Graph(s).cherry_parent(a,b) is not None for s in ss)
def cleanup(T,ss,F,a):
    assert proper(T,ss) and a in ss
    ss2=list(ss); ss2.remove(a)
    F2=[list(B) for B in F]; F2.remove([a])
    return Graph(T).restriction(set(labels(T))-{a}),ss2,F2

def contract_block(B,a,b,z):
    return [z]+[x for x in B if x not in (a,b)] if a in B else list(B)
def expand_block(B,a,b,z): return [y for x in B for y in ([a,b] if x==z else [x])]
def coalesce(F,a,b):
    A=next(B for B in F if a in B); B=next(B for B in F if b in B)
    if A is B: return [list(C) for C in F]
    assert len(A)==1 or len(B)==1, (F,a,b,'separated nonsingletons')
    # deterministic adapter: preserve a's block when possible; otherwise b's.
    keep,drop,endpoint=(A,B,b) if len(B)==1 else (B,A,a)
    return [list(C)+[endpoint] if C is keep else list(C) for C in F if C is not drop]

def exact(got,want,name):
    if got != want: raise AssertionError({'check':name,'got':got,'expected':want})
def compare_record(got,want):
    exact(got,want,'record equality'); return True

def check_fixture(f,qvalues):
    T,ss,a,b,z=(f[k] for k in ('T','ss','a','b','z'))
    exact(proper(T,ss),f['proper'],f['id']+' proper')
    exact(ready(T,ss,a,b,z),f['ready'],f['id']+' ready')
    FF=forests(T,ss); mn=min((cost(ss,F) for F in FF),default=None)
    exact(mn,f['minimum'],f['id']+' minimum')
    counts=collections.Counter(); details=[]
    if 'singleton' in f:
        x=f['singleton']; T2=f['cleanupT']; ss2=f['cleanupSS']
        for F in FF:
            gotT,gotSS,F2=cleanup(T,ss,F,x)
            compare_record([gotT,gotSS],[T2,ss2])
            assert agrees(T2,ss2,F2); exact(cost(ss,F),cost(ss2,F2),'singleton forward cost')
            counts['singletonForward']+=1
        for F2 in forests(T2,ss2):
            F=F2+[[x]]
            assert agrees(T,ss,F); exact(cost(ss,F),cost(ss2,F2),'singleton reverse cost')
            counts['singletonReverse']+=1
        exact(len(labels(T))-len(labels(T2)),1,'singleton strict drop')
        mn2=min(cost(ss2,F) for F in forests(T2,ss2))
        exact([mn<=q for q in qvalues],[mn2<=q for q in qvalues],'singleton all-q thresholds')
    if f['ready']:
        T2=Graph(T).contracted(a,b,z); ss2=[Graph(s).contracted(a,b,z) for s in ss]
        compare_record([T2,ss2],[f['contractT'],f['contractSS']])
        for F in FF:
            G=coalesce(F,a,b); assert agrees(T,ss,G); assert cost(ss,G)<=cost(ss,F)
            G2=[contract_block(B,a,b,z) for B in G]
            assert agrees(T2,ss2,G2); exact(len(G2),len(G),'contract block count'); exact(cost(ss,G),cost(ss2,G2),'contract cost')
            counts['coalesceForward']+=1
        for F2 in forests(T2,ss2):
            G=[expand_block(B,a,b,z) for B in F2]
            assert agrees(T,ss,G); exact(cost(ss,G),cost(ss2,F2),'expand cost'); exact(len(G),len(F2),'expand count')
            H=[contract_block(B,a,b,z) for B in G]
            compare_record(H,F2)
            counts['cherryReverse']+=1
        exact(len(ss),len(ss2),'source count'); exact(len(labels(T))-len(labels(T2)),1,'cherry strict drop')
        mn2=min(cost(ss2,F) for F in forests(T2,ss2)); exact(mn,mn2,'cherry all-Nat-q minimum threshold')
        exact([mn<=q for q in qvalues],[mn2<=q for q in qvalues],'cherry q truth vector')
    return {'id':f['id'],'minimum':mn,'agreements':len(FF),'transports':dict(counts),'qTruth':[mn is not None and mn<=q for q in qvalues]}

def main():
    p=argparse.ArgumentParser(); p.add_argument('--pilot',action='store_true'); p.add_argument('--out',required=True); a=p.parse_args()
    spec=json.loads((HERE/'EXPECTATIONS-v1.json').read_text()); begin=time.perf_counter(); rows=[]
    fixtures=spec['fixtures'][:4] if a.pilot else spec['fixtures']
    for f in fixtures:
        t=time.perf_counter(); r=check_fixture(f,spec['q']); r['seconds']=time.perf_counter()-t; rows.append(r)
    if not a.pilot:
        byid={f['id']:f for f in fixtures}
        for e in spec['agreements']:
            f=byid[e['fixture']]; T,ss,F=f['T'],f['ss'],e['F']; exact(agrees(T,ss,F),e['valid'],'explicit agreement'); exact(cost(ss,F),e['cost'],'explicit cost')
            if 'coalesced' in e:
                G=coalesce(F,f['a'],f['b']); compare_record(G,e['coalesced']); exact(cost(ss,G),e['coalescedCost'],'coalesce explicit cost')
            if 'cleanupF' in e: compare_record(cleanup(T,ss,F,f['singleton'])[2],e['cleanupF'])
            if 'contractF' in e: compare_record([contract_block(B,f['a'],f['b'],f['z']) for B in F],e['contractF'])
        for g in spec['geometry']:
            G=Graph(g['T']); compare_record(sorted(''.join(map(str,v)) for v in G.hull(g['B'])),g['hull']); compare_record(G.restriction(g['B']),g['restriction'])
            if 'C' in g:
                exact(disjoint(g['T'],[g['B'],g['C']]),g['disjoint'],'clearance original')
                exact(disjoint(g['T'],[g['addedB'],g['C']]),g['addedDisjoint'],'clearance weakened')
    record={'status':'CONTROLS-PASS','phase':'pilot' if a.pilot else 'fixed','startedUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'fixtures':rows,'expectedFixtureCount':len(fixtures),'completedFixtureCount':len(rows),'seconds':time.perf_counter()-begin,'expectationsSHA256':hashlib.sha256((HERE/'EXPECTATIONS-v1.json').read_bytes()).hexdigest()}
    exact(record['completedFixtureCount'],record['expectedFixtureCount'],'case denominator')
    pathlib.Path(a.out).write_text(json.dumps(record,indent=2)+'\n'); print(json.dumps({'status':record['status'],'fixtures':len(rows),'seconds':record['seconds']}))
if __name__=='__main__': main()
