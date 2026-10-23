#!/usr/bin/env python3
"""One-shot independent second-review checker; stdlib only, no imported oracle.
Exact forest enumeration is deliberate for small fixtures; no global proof claim.
"""
from dataclasses import dataclass
from itertools import combinations, product
from pathlib import Path
import json, time, hashlib, sys

BASE=Path(__file__).resolve().parent
ROOT=BASE.parents[3]

@dataclass
class Graph:
    vertices: set
    labels: dict
    arcs: dict  # ID -> (parent, child, original-arc provenance)
    def cut(self, ids):
        ids=set(ids)
        assert ids <= self.arcs.keys(), ('nonedge',ids-self.arcs.keys())
        return Graph(set(self.vertices),dict(self.labels),{e:a for e,a in self.arcs.items() if e not in ids})
    def children(self,v):
        return [(e,a[1]) for e,a in self.arcs.items() if a[0]==v]
    def parent(self,v):
        z=[(e,a[0]) for e,a in self.arcs.items() if a[1]==v]
        assert len(z)<=1
        return z[0] if z else None
    def desc(self,v):
        out={v}; stack=[v]
        while stack:
            for _,w in self.children(stack.pop()):
                assert w not in out
                out.add(w); stack.append(w)
        return out
    def labs(self,v):
        return {self.labels[w] for w in self.desc(v) if w in self.labels}
    def component_labs(self,v):
        seen={v}; stack=[v]
        while stack:
            z=stack.pop()
            for a,b,_ in self.arcs.values():
                if a==z and b not in seen: seen.add(b); stack.append(b)
                if b==z and a not in seen: seen.add(a); stack.append(a)
        return {self.labels[w] for w in seen if w in self.labels}
    def node(self,labs):
        target=set(labs)
        z=[v for v in self.vertices if self.labs(v)==target and v not in self.labels or v in self.labels and {self.labels[v]}==target]
        # rho has its own label; prevent it aliasing ordinary root cluster.
        z=[v for v in z if v not in self.labels or self.labels[v] in target]
        assert len(z)==1,(target,z)
        return z[0]
    def edge(self,labs):
        v=self.node(labs); p=self.parent(v); assert p
        return p[0]
    def path(self,a,c):
        def chain(v):
            out=[v]
            while self.parent(v):
                v=self.parent(v)[1]; out.append(v)
            return out
        aa,cc=chain(a),chain(c)
        u=next(v for v in aa if v in cc)
        ids=[]
        for chain_ in [aa,cc]:
            for v in chain_:
                if v==u: break
                ids.append(self.parent(v)[0])
        return set(ids),u
    def signature(self):
        g=reduce_graph(self)
        def visit(v):
            return (g.labels.get(v,''),tuple(sorted((visit(w) for _,w in g.children(v)))))
        roots=[v for v in g.vertices if g.parent(v) is None]
        return tuple(sorted(visit(v) for v in roots))
    def manifest(self):
        return {e:{'parent':a,'child':b,'origins':list(p)} for e,(a,b,p) in sorted(self.arcs.items())}

def tree(t, rho=True):
    vertices=set(); labels={}; arcs={}
    def build(s,v):
        vertices.add(v)
        if isinstance(s,str): labels[v]=s
        else:
            assert len(s)==2
            for i,child in enumerate(s):
                w=v+str(i); build(child,w); e='e:'+w; arcs[e]=(v,w,(e,))
    build(t,'n')
    if rho: vertices.add('rho'); labels['rho']='rho'; arcs['e:n']=('rho','n',('e:n',))
    return Graph(vertices,labels,arcs)

def reduce_graph(F):
    g=F.cut(set())
    while True:
        v=next((v for v in sorted(g.vertices) if v not in g.labels and len(g.children(v))<2),None)
        if v is None: break
        ch=g.children(v); pa=g.parent(v)
        if ch:
            ec,c=ch[0]
            if pa:
                ep,p=pa
                origins=g.arcs[ep][2]+g.arcs[ec][2]
                k='join['+','.join(origins)+']'
                g.arcs[k]=(p,c,origins)
            del g.arcs[ec]
        if pa: del g.arcs[pa[0]]
        g.vertices.remove(v)
    return g

def subsets(xs):
    xs=sorted(xs)
    for k in range(len(xs)+1):
        for z in combinations(xs,k): yield frozenset(z)

def yields(F):
    return {F.cut(E).signature() for E in subsets(F.arcs)}

def optimum(F1,F2):
    accepted=yields(F1)
    for E in subsets(F2.arcs):
        if F2.cut(E).signature() in accepted: return len(E),sorted(E)
    raise AssertionError('no singleton AF')

def norm(F,E,a,c):
    P,u=F.path(a,c); D=set(E)&P; out=set(E)-D
    if len(D)>=2 and F.parent(u): out.add(F.parent(u)[0])
    return frozenset(out)

def write(name,data):
    p=BASE/name; p.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    return str(p)

def controls():
    t0=time.perf_counter(); F=tree([['a','b'],'c']); twin=tree([['a','c'],'b'])
    assert F.signature()==tree([['b','a'],'c']).signature()
    assert F.signature()!=twin.signature()
    assert optimum(F,F)[0]==0 and optimum(F,twin)[0]==1
    ea=F.edge(['a']); reduced=reduce_graph(F.cut([ea])); ab=F.edge(['a','b'])
    expected=tuple(sorted([('a',()),('rho',(('',(('b',()),('c',()))),))]))
    assert reduced.signature()==expected,(reduced.signature(),expected)
    assert ab not in reduced.arcs
    assert reduce_graph(F).manifest()==F.manifest()
    assert F.cut(F.arcs).signature()==tuple(sorted((v,()) for v in ['a','b','c','rho']))
    return {'identical_optimum':0,'one_rearrangement_optimum':1,'null_edges_preserved':True,'all_cut_singletons':['a','b','c','rho'],'wrong_topology_rejected':True,'suppressed_edge_rejected':ab,'expected_single_cut_signature':expected,'elapsed_seconds':time.perf_counter()-t0}

def transport(F,a,c,x,K):
    P,u=F.path(a,c); v=F.parent(u)[1]
    assert F.parent(x)[1]==v
    pathvertices={a,c}|{z for e in P for z in F.arcs[e][:2]}
    B={e for e,(p,w,_) in F.arcs.items() if p in pathvertices-{a,c} and w not in pathvertices}
    assert len(B)==2,(B,P)
    assert B<=K and not K&P
    G=reduce_graph(F.cut(B)); C=K-B
    for e in F.arcs.keys()-B-P:
        assert e in G.arcs and G.arcs[e]==F.arcs[e],('unchanged',e)
    assert {x,u,v}<=G.vertices
    for w in [x,u,v]:
        assert F.parent(w)==G.parent(w)
    assert all(e in G.arcs and G.arcs[e]==F.arcs[e] for e in C)
    FG=F.cut(K); GG=G.cut(C)
    assert FG.signature()==GG.signature()
    left,right=reduce_graph(FG),reduce_graph(GG)
    assert (left.vertices,left.labels,left.manifest())==(right.vertices,right.labels,right.manifest())
    for w in [x,u,v]:
        assert FG.labs(w)==GG.labs(w)
        assert FG.component_labs(w)==GG.component_labs(w)
    assert len(K)==2+len(C)
    assert G.path(x,u)[0]=={F.parent(x)[0],F.parent(u)[0]}
    Cp=norm(G,C,x,u); Kp=B|Cp
    assert all(e in F.arcs and F.arcs[e]==G.arcs[e] for e in Cp)
    assert F.cut(Kp).signature()==G.cut(Cp).signature()
    left,right=reduce_graph(F.cut(Kp)),reduce_graph(G.cut(Cp))
    assert (left.vertices,left.labels,left.manifest())==(right.vertices,right.labels,right.manifest())
    for w in [x,u,v]:
        assert F.cut(Kp).labs(w)==G.cut(Cp).labs(w)
        assert F.cut(Kp).component_labs(w)==G.cut(Cp).component_labs(w)
    assert len(Kp)==2+len(Cp)
    return {'B':sorted(B),'P':sorted(P),'C':sorted(C),'Kprime':sorted(Kp),'second_path':sorted(G.path(x,u)[0]),'optional_parent':F.parent(v),'root_fragments':{w:sorted(FG.labs(w)) for w in [x,u,v]},'G_edges':G.manifest()}

def frozen():
    t0=time.perf_counter()
    spec=json.loads((BASE.parent/'two-stage-original-spec.json').read_text())
    F1,F=tree(spec['t1']),tree(spec['t2']); accepted=yields(F1)
    opt,wit=optimum(F1,F); assert opt==2
    a,c,x=[F.node([s]) for s in ['a','c','x']]
    B={F.edge(['b1']),F.edge(['b2'])}; rows=[]
    for names in spec['positive_cutsets']:
        E={F.edge([s]) for s in names}
        assert F.cut(E).signature() in accepted
        K=norm(F,E|B,a,c)
        second=transport(F,a,c,x,K); Kp=set(second['Kprime'])
        assert [len(E),len(K),len(Kp)]==[2,3,2]
        assert Kp==B and F.cut(K).signature() in accepted and F.cut(Kp).signature() in accepted
        rows.append({'names':names,'E':sorted(E),'K':sorted(K),'Kprime':sorted(Kp),'counts':[len(E),len(K),len(Kp)],'transport':second})
    bad=[]
    for e in B:
        assert F.cut(B-{e}).signature() not in accepted
        bad.append({'deleted':e,'AF':False})
    G=reduce_graph(F.cut(B)); suppressed=next(e for e in F.path(a,c)[0] if e not in G.arcs)
    assert not(suppressed in G.arcs and F.arcs[suppressed]==G.arcs[suppressed])
    variants=[]
    for mode in ['rho_singleton','no_rho_component']:
        H=F.cut(['e:n']) if mode=='rho_singleton' else tree(spec['t2'],rho=False)
        J=F1.cut(['e:n']) if mode=='rho_singleton' else tree(spec['t1'],rho=False)
        acc=yields(J); hrows=[]
        for names in spec['positive_cutsets']:
            E={H.edge([s]) for s in names}; K=norm(H,E|B,a,c)
            out=transport(H,a,c,x,K); Kp=set(out['Kprime'])
            assert [len(E),len(K),len(Kp)]==[2,3,2] and out['optional_parent'] is None
            assert H.cut(E).signature() in acc and H.cut(K).signature() in acc and H.cut(Kp).signature() in acc
            hrows.append({'E':sorted(E),'K':sorted(K),'Kprime':sorted(Kp),'counts':[2,3,2],'optional_parent':None})
        variants.append({'mode':mode,'optimum':optimum(J,H)[0],'rows':hrows})
    return {'optimum':opt,'optimum_witness':wit,'rows':rows,'bad_final_cuts':bad,'suppressed_corruption_rejected':suppressed,'root_variants':variants,'elapsed_seconds':time.perf_counter()-t0}

def boundaries():
    rows=[]
    for name in ['compound-boundary-frozen.json','partial-boundary-frozen.json']:
        d=json.loads((BASE.parent/'edge_route'/name).read_text()); F1,F=tree(d['T1']),tree(d['T2'])
        E={F.edge(s) for s in d['E_clusters']}; accepted=yields(F1)
        a=F.node(d.get('a_cluster',['a'])); c=F.node(d.get('c_cluster',['c']))
        full=norm(F,E,a,c); partial=E-{F.edge(['a'])}
        assert F.cut(E).signature() in accepted
        opt,ow=optimum(F1,F); assert opt==1
        if name.startswith('compound'):
            assert len(E)==3 and not F.cut(E).labs(c)
            assert F.cut(full).signature() not in accepted
        else:
            assert len(E)==2 and F.cut(partial).signature() not in accepted and F.cut(full).signature() in accepted
        rows.append({'fixture':name,'original_AF':True,'E':sorted(E),'cut_count':len(E),'optimum':opt,'optimum_witness':ow,'full_normalized':sorted(full),'full_AF':F.cut(full).signature() in accepted,'partial_restoration':sorted(partial),'partial_AF':F.cut(partial).signature() in accepted,'c_fragment':sorted(F.cut(E).labs(c)),'is_minimum_consumer_counterexample':False})
    return rows

def geometry(limit=None):
    t0=time.perf_counter(); cases=0; graphs=0; empty=0; branchcounts={}; witness=None
    # Ordered rooted shapes: two corridor side branches in all three left/right allocations;
    # compound a,c,x and b subtrees, optional outside context, rho/root variations.
    for compound in [False,True]:
      A=['a1','a2'] if compound else 'a'; C=['c1','c2'] if compound else 'c'; X=['x1','x2'] if compound else 'x'
      al=['a1','a2'] if compound else ['a']; cl=['c1','c2'] if compound else ['c']; xl=['x1','x2'] if compound else ['x']
      for shape in [0,1,2]:
       U=[[[A,'b1'],'b2'],C] if shape==0 else ([[A,'b1'],[C,'b2']] if shape==1 else [A,[[C,'b1'],'b2']])
       for context in [False,True]:
        T=[[U,X],'z'] if context else [U,X]
        for mode in ['rho','rho_singleton','no_rho_component']:
         F=tree(T,rho=mode!='no_rho_component')
         if mode=='rho_singleton': F=F.cut(['e:n'])
         a,c,x=F.node(al),F.node(cl),F.node(xl); P,u=F.path(a,c); B={F.edge(['b1']),F.edge(['b2'])}
         graphs+=1
         for Cset in subsets(F.arcs.keys()-B-P):
          K=B|Cset
          out=transport(F,a,c,x,K); cases+=1
          if not F.cut(K).labs(u) or not F.cut(K).labs(x): empty+=1
          d=len(set(out['second_path']) & Cset); branchcounts[d]=branchcounts.get(d,0)+1
          if witness is None and not F.cut(K).labs(u) and not F.cut(K).labs(x): witness={'shape':T,'root_mode':mode,'K':sorted(K),'data':out}
          if limit and cases>=limit:
           return {'cases':cases,'graphs':graphs,'empty_root_cases':empty,'second_cut_counts':branchcounts,'elapsed_seconds':time.perf_counter()-t0,'limited':True,'empty_root_witness':witness}
    return {'cases':cases,'graphs':graphs,'empty_root_cases':empty,'second_cut_counts':branchcounts,'elapsed_seconds':time.perf_counter()-t0,'limited':False,'empty_root_witness':witness}

if __name__=='__main__':
    mode=sys.argv[1] if len(sys.argv)>1 else 'controls'
    if mode=='controls': result=controls()
    elif mode=='frozen': result=frozen()
    elif mode=='boundaries': result=boundaries()
    elif mode=='geometry': result=geometry(int(sys.argv[2]) if len(sys.argv)>2 else None)
    else: raise ValueError(mode)
    path=write(mode+('-pilot' if len(sys.argv)>2 else '')+'.json',result)
    print(json.dumps({'mode':mode,'output':path,'result':result},sort_keys=True))
