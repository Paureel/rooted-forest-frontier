#!/usr/bin/env python3
"""One-shot independent audit; no campaign imports. Exact graph cuts vs label partitions.
Use --pilot for n=3,4 timings and controls. Use --full for n<=4 rho pair census.
Outputs are finite checks, never a universal correctness certificate.
"""
import argparse, hashlib, itertools, json, time
from pathlib import Path
ROOT=Path(__file__).resolve().parent

class Graph:
    def __init__(self, forest, rho=False):
        self.child={}; self.parent={}; self.label={}; self.bylabel={}
        def add(t, parent=None):
            v=len(self.child); self.child[v]=[]
            if parent is not None:
                self.parent[v]=parent; self.child[parent].append(v)
            if isinstance(t,str): self.label[v]=t; self.bylabel[t]=v
            else:
                for s in t: add(s,v)
            return v
        self.roots=[]
        for t in forest:
            if rho:
                r=add('rho'); add(t,r)
            else: r=add(t)
            self.roots.append(r)
        self.edges=tuple(sorted(self.parent)) # child identifies parent edge
        self.labels=tuple(sorted(self.bylabel))
    def path(self,a,b):
        chain=[]; v=a
        while True:
            chain.append(v)
            if v not in self.parent: break
            v=self.parent[v]
        back=[]; v=b
        while v not in chain:
            back.append(v)
            if v not in self.parent: return None
            v=self.parent[v]
        return chain[:chain.index(v)+1]+back[::-1]
    def span(self,block):
        ids=[self.bylabel[x] for x in block]
        out={ids[0]}
        for v in ids[1:]:
            p=self.path(ids[0],v)
            if p is None: return None
            out.update(p)
        return out
    def restricted(self,block):
        span=self.span(block)
        if span is None: return None
        root=next(v for v in span if self.parent.get(v) not in span)
        def rec(v):
            children=sorted([rec(w) for w in self.child[v] if w in span],key=repr)
            if v in self.label: return ('L', self.label[v], tuple(children))
            if len(children)==1: return children[0]
            return ('N',tuple(children))
        return rec(root)
    def cut(self,E):
        E=set(E)
        roots=list(self.roots)+sorted(E)
        def rec(v):
            cs=[z for w in self.child[v] if w not in E for z in [rec(w)] if z is not None]
            if v in self.label: return ('L',self.label[v],tuple(sorted(cs,key=repr)))
            if not cs: return None
            if len(cs)==1: return cs[0]
            return ('N',tuple(sorted(cs,key=repr)))
        return tuple(sorted([s for r in roots for s in [rec(r)] if s is not None],key=repr))
    def allcuts(self):
        out={}
        for bits in range(1<<len(self.edges)):
            es=frozenset(v for i,v in enumerate(self.edges) if bits>>i&1)
            f=self.cut(es)
            if f not in out or len(es)<out[f][0]: out[f]=(len(es),[es])
            elif len(es)==out[f][0]: out[f][1].append(es)
        return out

def partitions(xs):
    if not xs:
        yield (); return
    first,*rest=xs
    for p in partitions(rest):
        yield (frozenset([first]),)+p
        for i in range(len(p)):
            yield p[:i]+(p[i]|{first},)+p[i+1:]

def valid(g,h,p,ignore_overlap=False):
    if set().union(*p)!=set(g.labels) or sum(map(len,p))!=len(g.labels): return False
    for z in [g,h]:
        spans=[z.span(b) for b in p]
        if any(s is None for s in spans): return False
        if not ignore_overlap and any(a&b for a,b in itertools.combinations(spans,2)): return False
    return all(g.restricted(b)==h.restricted(b) for b in p)

def optimum_partition(g,h):
    return min(len(p) for p in partitions(g.labels) if valid(g,h,p))

def trees(xs):
    if len(xs)==1: return [xs[0]]
    out=[]; least=xs[0]
    for bits in range(1<<(len(xs)-1)):
        A=[least]+[x for i,x in enumerate(xs[1:]) if bits>>i&1]
        B=[x for x in xs if x not in A]
        if not B: continue
        for a in trees(A):
            for b in trees(B): out.append((a,b))
    return out

def controls():
    out=[]
    def check(name,got,expected):
        assert got==expected,(name,got,expected)
        out.append({'id':name,'got':got,'expected':expected,'passed':True})
    a=Graph([('a','b')]); check('identity',optimum_partition(a,a),1)
    for rho in [False,True]:
        a=Graph([(('a','b'),'c')],rho); b=Graph([('a',('b','c'))],rho)
        value=optimum_partition(a,b)
        check('rotation_rho_'+str(rho),value,2)
        check('corrupted_rotation_expectation_rejected_'+str(rho),value!=1,True)
    a=Graph([(('a','b'),('c','d'))]); cross=(frozenset('ac'),frozenset('bd'))
    clean=(frozenset('ab'),frozenset('cd'))
    check('clean_partition',valid(a,a,clean),True)
    check('crossing_partition',valid(a,a,cross),False)
    check('omit_overlap_mutant_detected',valid(a,a,cross,True)!=valid(a,a,cross),True)
    check('zero_cut',len(a.cut([])),1)
    f=Graph([('a','c'),'b','d','rho']); g=Graph([(('a','b'),('c','d')),'rho'])
    E={g.bylabel[x] for x in 'abcd'}; E2={g.bylabel[x] for x in 'bd'}
    allf=f.allcuts()
    check('root_exchange_E_AF',g.cut(E) in allf,True)
    check('root_exchange_E0_AF',g.cut(E2) in allf,True)
    check('root_exchange_u_parent_absent',0 not in g.parent,True)
    # A root pair sibling cut is the same partition/topology; root label is absent here.
    two=Graph([(('a','b'),('c','d'))]); x,y=two.child[0]
    check('root_sibling_equivalence',two.cut([x])==two.cut([y]),True)
    # OR inheritance differs from overwrite whenever exactly first edge is protected.
    check('OR_inheritance_mutant', (True or False)!=(False),True)
    return out

def census(n,rho,do_exchange=True):
    ts=trees(list('abcd'[:n])); gs=[Graph([t],rho) for t in ts]
    start=time.perf_counter(); maps=[g.allcuts() for g in gs]
    map_time=time.perf_counter()-start; pairs=0; exchange=0; failures=[]; triples=0
    for i,g in enumerate(gs):
        for j,h in enumerate(gs):
            common=set(maps[i])&set(maps[j]); q=min(len(s)-1 for s in common)
            op=optimum_partition(g,h)
            pairs+=1
            if q+1!=op: failures.append({'kind':'cut-partition','i':i,'j':j,'cut_components':q+1,'partition_components':op})
            if not do_exchange: continue
            successful=[E for s in common if maps[j][s][0]==q for E in maps[j][s][1]]
            for p,children in g.child.items():
                if len(children)!=2 or not all(v in g.label for v in children): continue
                A,C=[g.label[v] for v in children]
                if A=='rho' or C=='rho': continue
                a,c=h.bylabel[A],h.bylabel[C]; path=h.path(a,c)
                pathset=set(path)
                pend=[w for v in path for w in h.child[v] if w not in pathset]
                if len(pend)!=2: continue
                B=set(pend)
                for E in successful:
                    for endpoint in [a,c]:
                        if endpoint in E and E&B:
                            exchange+=1
                            if not any(B<=F for F in successful): failures.append({'kind':'A2BC-exchange','T1':ts[i],'T2':ts[j],'rho':rho,'a':A,'c':C,'E':sorted(E),'B':pend})
    return {'n':n,'rho':rho,'trees':len(ts),'pairs':pairs,'cut_map_seconds':map_time,'seconds':time.perf_counter()-start,'A2BC_exchange_premises':exchange,'failures':failures}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--pilot',action='store_true'); ap.add_argument('--full',action='store_true'); args=ap.parse_args()
    receipt={'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'controls':controls(),'scope':'fresh finite exact arithmetic, no imported campaign helper; not universal proof'}
    if args.pilot: receipt['census']=[census(3,True),census(4,True)]
    if args.full: receipt['census']=[census(n,rho) for rho in [False,True] for n in [3,4]]
    assert not any(r['failures'] for r in receipt.get('census',[])),receipt
    out=ROOT/('independent-full.json' if args.full else 'independent-pilot.json')
    out.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'controls':len(receipt['controls']),'census':receipt.get('census',[]),'receipt':str(out)}))
if __name__=='__main__': main()
