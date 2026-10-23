#!/usr/bin/env python3
"""One-shot independent finite CB4 certificate/coverage review; frozen design v1."""
from pathlib import Path
import sys,json,itertools,time,copy,hashlib,argparse
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE.parent))
import independent_cb1 as X
ROOT=BASE.parents[1]
sys.path.insert(0,str(ROOT))
import guarded_frontier as G
import exact_conflicts as PRODUCTION
OUT=Path('research/rmaf/results')


def rooted_clades(vertices,parent,leaf):
    D={v:set() for v in vertices}
    for a,v in leaf.items():
        while v is not None:D[v].add(a);v=parent[v]
    return {v:frozenset(B) for v,B in D.items()}

def map_model(P,I):
    pc=rooted_clades(P.parent,P.parent,P.leaf);ic=rooted_clades(I.adj,I.parent,I.leaf)
    assert len(set(pc.values()))==len(pc) and set(pc.values())==set(ic.values())
    inv={c:v for v,c in ic.items()};V={v:inv[c] for v,c in pc.items()}
    assert set(P.labels)==set(I.labels)
    assert {a:V[v] for a,v in P.leaf.items()}==I.leaf
    IE={e:i for i,e in enumerate(I.edges)};E={i:IE[(V[u],V[v])] for i,(u,v) in enumerate(P.edges)}
    assert len(E)==len(set(E.values()))==len(I.edges)
    assert {V[v]:None if p is None else V[p] for v,p in P.parent.items()}==I.parent
    return V,E

class Model:
    def __init__(self,s,t,b):
        self.S,self.T=X.Tree(s),X.Tree(t);self.PS,self.PT=G.core.validate_input(s,t,b)
        self.SV,self.SE=map_model(self.PS,self.S);self.TV,self.TE=map_model(self.PT,self.T)

def graph_parts(S,V,cuts):
    unseen=set(V);P=[]
    while unseen:
        todo=[min(unseen)];unseen.remove(todo[0]);block=set()
        while todo:
            v=todo.pop();block.add(v)
            for w,e in S.adj[v]:
                if w in unseen and e not in cuts:unseen.remove(w);todo.append(w)
        L=frozenset(a for a,v in S.leaf.items() if v in block)
        P.append((L,frozenset(block)))
    return sorted(P,key=lambda z:tuple(sorted(z[0])))

def topo(x):
    if x is None or isinstance(x,str):return x
    assert isinstance(x,(list,tuple)) and len(x)==2
    return tuple(sorted((topo(a) for a in x),key=repr))

def local_agreement(M,L,P,V=None):
    flat=[a for B in P for a in B]
    if len(flat)!=len(set(flat)) or set(flat)!=set(L) or any(not B for B in P):return False
    us=set();ut=set()
    for B in P:
        if X.restriction(M.S.raw,B)!=X.restriction(M.T.raw,B):return False
        s,t=M.S.support(B),M.T.support(B)
        if us&s or ut&t or (V is not None and not s<=V):return False
        us|=s;ut|=t
    return True

def check_impl(M,b,K):
    S,T=M.S,M.T;pcuts=K['original_source_edge_indices'];assert len(pcuts)==len(set(pcuts))
    assert all(isinstance(e,int) and not isinstance(e,bool) and e in M.SE for e in pcuts)
    cuts={M.SE[e] for e in pcuts};assert K['precut_cost']==len(cuts)<=b
    parts=graph_parts(S,S.adj,cuts);assert all(L for L,V in parts)
    assert len(parts)==(len(cuts)+1 if S.labels else 0)
    assert len(parts)==len(K['components']);spans=[];compatible=[];costs=[];score_parts=[]
    for (L,V),C in zip(parts,K['components']):
        assert C['original_labels']==sorted(L)
        vertices=C['full_original_vertices'];assert len(vertices)==len(set(vertices)) and {M.SV[v] for v in vertices}==V
        assert topo(C['source_restriction'])==X.restriction(S.raw,L)
        support=C['target_support'];assert len(support)==len(set(support)) and {M.TV[v] for v in support}==T.support(L)
        spans.append(T.support(L));compatible.append(X.restriction(S.raw,L)==X.restriction(T.raw,L))
        W=C['local_witness'];P=tuple(frozenset(B) for B in W['pieces']);assert local_agreement(M,L,P,V)
        assert len(W['target_supports'])==len(P)
        for B,st in zip(P,W['target_supports']):assert len(st)==len(set(st)) and {M.TV[v] for v in st}==T.support(B)
        edges=W['original_local_edge_indices'];assert len(edges)==len(set(edges))
        assert all(isinstance(e,int) and not isinstance(e,bool) and e in M.SE for e in edges)
        localcuts={M.SE[e] for e in edges};assert not cuts&localcuts
        assert all(S.edges[e][0] in V and S.edges[e][1] in V for e in localcuts)
        localparts=graph_parts(S,V,localcuts);assert all(B for B,Z in localparts)
        assert {B for B,Z in localparts}==set(P)
        assert W['cost']==len(localcuts)==len(P)-1<=b//2
        costs.append(W['cost']);score_parts.append({'labels':sorted(L),'vertices':sorted(V),'witness_cost':W['cost'],'pieces':[sorted(B) for B in P]})
    pure=all(all(sum(w in spans[i] for w,e in T.adj[v])==2 and sum(w in spans[j] for w,e in T.adj[v])==2 for v in spans[i]&spans[j]) for i in range(len(spans)) for j in range(i))
    ct=all(q or len(L)==3 for q,(L,V) in zip(compatible,parts))
    assert pure or ct
    assert K['pure']==pure and K['compatible_triple']==ct
    assert K['terminal_class']==('compatible-triple' if ct else 'pure-bridge')
    assert K['original_unmarked_tau_upper_bound']==max(costs,default=0)<=b//2
    return {'parts':score_parts,'precut_partition':[sorted(L) for L,V in parts],'pure':pure,'compatible_triple':ct,'actual_tau':None}

def check(M,b,K):
    try:return True,check_impl(M,b,K)
    except (AssertionError,KeyError,TypeError,ValueError,IndexError) as e:return False,type(e).__name__+': '+str(e)

def optimum_partitions(M):
    best=len(M.S.labels)+1;out=[]
    for P in X.partitions(M.S.labels):
        if len(P)>best:continue
        if X.agreement(M.S,M.T,P):
            if len(P)<best:best=len(P);out=[]
            out.append(P)
    return max(0,best-1),out

def survivors(opts,parts):return sum(all(any(B<=frozenset(L) for L in parts) for B in P) for P in opts)

def local_distance(M,L,V):
    best=len(L)
    for P in X.partitions(tuple(sorted(L))):
        if len(P)<=best and local_agreement(M,L,P,V):best=len(P)
    return max(0,best-1)

def controls():
    t=time.perf_counter();P=json.loads(Path('research/rmaf/results/algorithm-balanced-cover-continue-cb4-controls.json').read_text());records=[]
    for i,f in enumerate(P['controls']):
        M=Model(f['source'],f['target'],f['budget']);K=f['certificate'];ok,D=check(M,f['budget'],K);assert ok,D
        if 'expected_tau_upper_bound' in f:assert K['original_unmarked_tau_upper_bound']==f['expected_tau_upper_bound']
        if f.get('pure_crossed_pair'):assert D['pure'] and len(D['precut_partition'])==2
        records.append({'control':i,'verified':True})
    f=P['controls'][3];M=Model(f['source'],f['target'],2);K=f['certificate'];caught=[]
    for kind in ['local-cost-plus-one','local-target-support-minus-one','full-source-vertex-omitted','false-half-budget-zero']:
        Q=copy.deepcopy(K);b=2
        if kind=='local-cost-plus-one':Q['components'][0]['local_witness']['cost']+=1
        if kind=='local-target-support-minus-one':Q['components'][0]['local_witness']['target_supports'][0]=[-1]
        if kind=='full-source-vertex-omitted':Q['components'][0]['full_original_vertices'].pop()
        if kind=='false-half-budget-zero':b=0
        assert not check(M,b,Q)[0];caught.append(kind)
    f=json.loads((BASE/'CONTROLS-v1.json').read_text())['coverage_control'];M=Model(f['source'],f['target'],1);v,opts=optimum_partitions(M);assert v==1
    clades=rooted_clades(M.PS.parent,M.PS.parent,M.PS.leaf)
    def guard_clade(L):
        e=next(e for e,(u,v) in enumerate(M.PS.edges) if clades[v]==frozenset(L));K=G.guard(M.PS,M.PT,1,1<<e);assert K is not None
        ok,D=check(M,1,K);assert ok,D
        return survivors(opts,D['precut_partition'])
    bad=guard_clade(['c','d']);good=guard_clade(['b']);assert bad==0 and good>0
    result={'status':'CONTROLS_PASS','positive_controls':records,'corruptions_caught':caught,'coverage_bad_guard_survivors':bad,'coverage_clean_guard_survivors':good,'seconds':time.perf_counter()-t,'instrument_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (OUT/'algorithm-balanced-cover-continue-review-cb4-controls-v1.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result));return result

def covers():
    t=time.perf_counter();F=json.loads((BASE.parent/'CONTROLS-frozen-v1.json').read_text())['ordinary'];R=json.loads(Path('research/rmaf/results/algorithm-balanced-cover-continue-cb4-controls.json').read_text());expected={r['id']:r for r in R['rows']};records=[];totalcerts=0;maxlocal=0
    for f in F:
        M=Model(f['source'],f['target'],f['optimum']);v,opts=optimum_partitions(M);assert v==f['optimum']
        for b in [v,v+2]:
            saved={n:getattr(PRODUCTION,n) for n in ['partitions','oracle','packing','exact_row']}
            def banned(*a,**k):raise AssertionError('production called a scoring oracle')
            try:
                for n in saved:setattr(PRODUCTION,n,banned)
                Z=G.generate(f['source'],f['target'],b)
            finally:
                for n,q in saved.items():setattr(PRODUCTION,n,q)
            old=next(c for c in expected[f['id']]['cases'] if c['budget']==b);assert Z==old['generation']
            certs=[]
            for K in Z['certificates']:
                ok,D=check(M,b,K);assert ok,(f['id'],b,D)
                distances=[]
                C={M.SE[e] for e in K['original_source_edge_indices']}
                for (L,V),W in zip(graph_parts(M.S,M.S.adj,C),D['parts']):
                    d=local_distance(M,L,V);assert d<=W['witness_cost']<=b//2;distances.append(d)
                D['actual_tau']=max(distances,default=0);D['local_distances']=distances
                D['surviving_original_optima']=survivors(opts,D['precut_partition']);certs.append(D)
                totalcerts+=1;maxlocal=max(maxlocal,len(distances))
            assert certs and any(d['surviving_original_optima']>0 for d in certs)
            assert [d['surviving_original_optima'] for d in certs]==old['surviving_original_optima_by_output']
            records.append({'id':f['id'],'budget':b,'optimum':v,'original_optimal_partitions':len(opts),'emitted_certificates':len(certs),'certificates':certs,'generation':Z,'literal_receipt_matches':True,'production_oracles_blocked':True})
    assert len(records)==18
    result={'status':'ALL_18_GUARDED_COVERS_CONFIRMED','covers':len(records),'emitted_certificates_checked':totalcerts,'rows':records,'seconds':time.perf_counter()-t,'scope':'finite independent feasibility/local-distance/coverage checks; C1 universal source proof, terminal completion and alpha remain open','instrument_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    assert result['seconds']<10
    (OUT/'algorithm-balanced-cover-continue-review-cb4-covers-v1.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['status','covers','emitted_certificates_checked','seconds']}))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--covers',action='store_true');a=ap.parse_args()
    if a.covers:covers()
    else:controls()
