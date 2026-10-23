#!/usr/bin/env python3
"""One-shot GLOBAL-Q finite witness search, intentionally not a toolkit tool.
Fresh source-edge deletion enumeration; no production/X0 imports or caches.
Exact instrument only: never called by a proposed generator.
"""
import itertools, json, time, hashlib
from pathlib import Path
from telemetry import step, metric, gate, artifact
ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT/'results/algorithm-balanced-cover-quotient-probe.json'

def tup(t):
    return t if isinstance(t,str) else tuple(tup(x) for x in t)
def canon(t):
    return t if isinstance(t,str) else tuple(sorted((canon(t[0]),canon(t[1])),key=repr))
def restrict(t,B):
    if isinstance(t,str): return t if t in B else None
    a,b=restrict(t[0],B),restrict(t[1],B)
    if a is None: return b
    if b is None: return a
    return canon((a,b))
class Tree:
    def __init__(self,t):
        self.t=t; self.ch={};self.label={};self.parent={};self.edges=[]
        def add(x,p=None):
            v=len(self.ch);self.ch[v]=[]
            if p is not None:
                self.parent[v]=p;self.edges.append((p,v));self.ch[p].append(v)
            if isinstance(x,str):self.label[v]=x
            else:
                add(x[0],v);add(x[1],v)
            return v
        self.root=add(t);self.vertices=set(self.ch);self.labels=set(self.label.values())
    def support(self,B):
        ids=[v for v,x in self.label.items() if x in B]
        if len(ids)==1:return set(ids)
        paths=[]
        for v in ids:
            p=[]
            while True:
                p.append(v)
                if v not in self.parent:break
                v=self.parent[v]
            paths.append(p)
        common=set(paths[0])
        for p in paths[1:]:common.intersection_update(p)
        lca=next(v for v in paths[0] if v in common)
        out=set()
        for p in paths:
            for v in p:
                out.add(v)
                if v==lca:break
        return out
    def certificate(self,cuts):
        cuts=set(cuts)
        if not cuts.issubset(set(self.edges)):return None
        adj={v:[] for v in self.vertices}
        for a,b in self.edges:
            if (a,b) not in cuts:adj[a].append(b);adj[b].append(a)
        unseen=set(self.vertices); comps=[]
        while unseen:
            todo=[min(unseen)];part=set()
            while todo:
                v=todo.pop()
                if v in part:continue
                part.add(v);todo.extend(w for w in adj[v] if w not in part)
            unseen.difference_update(part)
            L=frozenset(self.label[v] for v in part if v in self.label)
            if not L:return None
            comps.append((L,part))
        assert len(comps)==len(cuts)+1
        return comps

def agreement(S,T,blocks):
    supports=[]
    for B in blocks:
        if restrict(S.t,B)!=restrict(T.t,B):return False
        h=T.support(B)
        if any(h&g for g in supports):return False
        supports.append(h)
    return True

def optima(S,T):
    examined=0
    for k in range(len(S.labels)):
        found=[]
        for E in itertools.combinations(S.edges,k):
            examined+=1
            F=S.certificate(E)
            if F is not None and agreement(S,T,[L for L,_ in F]):
                found.append({'cuts':E,'blocks':[sorted(L) for L,_ in F]})
        if found:return k,found,examined
    raise AssertionError('singleton forest was not found')

def star_balance(b,r):return b-r<=b//2

def main():
    started=time.perf_counter(); controls=json.loads((Path(__file__).with_name('CONTROLS-v1.json')).read_text())
    rows=[]
    with step('check',tool='GLOBAL-Q known-truth'):
        for f in controls['positive']:
            S,T=Tree(tup(f['S'])),Tree(tup(f['T']))
            k,fs,n=optima(S,T)
            assert k==f['opt'],(f['id'],k,f['opt'])
            rows.append({'id':f['id'],'actual_opt':k,'expected_opt':f['opt'],'passed':True,'examined_source_cut_sets':n})
        neg=[]
        for f in controls['corruptions']:
            if f['id']=='wrong-topology':
                k,_,_=optima(Tree(tup(f['S'])),Tree(tup(f['T'])))
                caught=k!=f['claimed_opt']
            elif f['id']=='empty-source-piece':
                caught=Tree(tup(f['S'])).certificate([tuple(e) for e in f['cuts']]) is None
            else:caught=not star_balance(f['spokes'],1)
            assert caught,f['id'];neg.append({'id':f['id'],'caught':True})
    gate('known_truth','passed',detail='4 literal optimum controls and 3 planted corruptions executed; finite oracle development only')
    S=Tree(tup([[[[['a','b'],'c'],'d'],'e'],'f']))
    T=Tree(tup([['a','c'],[['b','e'],['d','f']]]))
    with step('compute',tool='GLOBAL-Q quotient pilot'):
        tic=time.perf_counter();k,fs,n=optima(S,T);seconds=time.perf_counter()-tic
        leafcuts=tuple(e for e in S.edges if S.label.get(e[1]) in {'b','d','f'})
        F=S.certificate(leafcuts)
        star_witness={'source':S.t,'target':T.t,'opt':k,'examined_source_cut_sets':n,'optimal_realization_count':len(fs),'pilot_seconds':seconds,'candidate_star_cuts':leafcuts,'candidate_star_is_optimum':len(leafcuts)==k and agreement(S,T,[L for L,_ in F])}
        if star_witness['candidate_star_is_optimum']:
            ids={v:i for i,(_,support) in enumerate(F) for v in support}
            q=[(ids[a],ids[b]) for a,b in leafcuts]
            degrees={i:sum(i in e for e in q) for i in range(len(F))}
            checks=[]
            for e in leafcuts:
                partial=S.certificate([e]);remaining=set(leafcuts)-{e}
                counts=[sum(a in support and b in support for a,b in remaining) for _,support in partial]
                local=[]
                for L,_ in partial:
                    d,_,_=optima(Tree(restrict(S.t,L)),Tree(restrict(T.t,L)))
                    local.append({'labels':sorted(L),'d':d})
                checks.append({'one_edge':e,'quotient_residual_counts':counts,'tau':max(x['d'] for x in local),'local':local,'half_budget':all(x['d']<=k//2 for x in local)})
            star_witness.update({'quotient_edges':q,'quotient_degrees':degrees,'one_edge_checks':checks,'Q2_ONE_refuted':all(max(row['quotient_residual_counts'])>k//2 for row in checks)})
        metric('completed',1,total=1,unit='pair')
    result={'kind':'GLOBAL-Q development witness, not cover verification','lineage':'fresh standard-library source edge deletion; never reads X0/parent/production implementations','controls':rows,'negative_controls':neg,'pilot':star_witness,'elapsed_seconds':time.perf_counter()-started,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    OUT.write_text(json.dumps(result,indent=2)+'\n');artifact(str(OUT))
    print(json.dumps({'controls_passed':len(rows),'corruptions_caught':len(neg),'opt':k,'candidate_star_is_optimum':star_witness['candidate_star_is_optimum'],'Q2_ONE_refuted':star_witness.get('Q2_ONE_refuted'),'pilot_seconds':seconds,'output':str(OUT)}))
if __name__=='__main__':main()
