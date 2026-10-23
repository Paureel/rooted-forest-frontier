"""One-shot 2B original-edge transport adversary. Reuses the existing independent
edge oracle, never component-route code. Oracle controls write only in this v2 dir.
"""
from pathlib import Path
import sys,json,time,itertools as it,hashlib
HERE=Path(__file__).resolve().parent;EDGE=HERE.parent;ROOT=EDGE.parents[4]
sys.path.insert(0,str(EDGE))
import adversary as old
old.RESULTS=HERE
Graph=old.Graph
RESULTS=ROOT/'research/rmaf/results'

def frag(F,cuts,v):
 H=F.cut(cuts)
 return sorted(lab for w,lab in H.labels.items() if H.root(w)==H.root(v)) if v in H.nodes else None

def descendant_frag(F,cuts,v):
 H=F.cut(cuts);below=F.descendants(v)
 return sorted(lab for w,lab in H.labels.items() if w in below and H.root(w)==H.root(v))

def exact_yield(A,B):
 X,Y=A.yielded_graph(),B.yielded_graph()
 return X.parent==Y.parent and X.labels==Y.labels

def canon(F):return sorted([(sorted(b),s) for b,s in F.components()],key=repr)
def structural(F,a,c,x):
 P,u=F.path(a,c);v=F.parent[u];assert v is not None and F.parent[x]==v and x!=u
 verts=set(P)|{u};B=frozenset(w for q in verts-{a,c} for w in F.children[q] if w not in verts)
 assert len(B)==2
 assert all(F.cluster(q) for q in [a,c,x])
 G=F.cut(B).yielded_graph()
 unchanged={e for e in F.edges-B if e in G.edges and F.parent[e]==G.parent[e]}
 assert F.edges-(B|P)<=unchanged
 assert {x,u,v}<=G.nodes
 assert G.parent[x]==v and G.parent[u]==v and G.parent[v]==F.parent[v]
 q,gg=G.path(x,u);assert q==frozenset([x,u]) and gg==v
 altered=[{'edge':e,'before_parent':F.parent[e],'after_parent':G.parent.get(e),'after_present':e in G.edges} for e in sorted(F.edges-B-unchanged)]
 return {'P':P,'u':u,'v':v,'B':B,'G':G,'unchanged':unchanged,'altered':altered}

def check_transport(F,a,c,x,K):
 S=structural(F,a,c,x);B,P,G,u,v=S['B'],S['P'],S['G'],S['u'],S['v'];assert B<=K and not K&P
 C=K-B
 assert all(e in G.edges and G.parent[e]==F.parent[e] for e in C)
 assert canon(G.cut(C))==canon(F.cut(K)) and exact_yield(G.cut(C),F.cut(K))
 assert frag(G,C,x)==frag(F,K,x) and frag(G,C,u)==frag(F,K,u)
 assert descendant_frag(G,C,x)==descendant_frag(F,K,x) and descendant_frag(G,C,u)==descendant_frag(F,K,u)
 assert len(K)==2+len(C)
 Cprime,removed,_,pe=old.normalization(G,x,u,C);Kprime=B|Cprime
 assert pe==(v if F.parent[v] is not None else None)
 assert Cprime<=G.edges and not Cprime&(B|P)
 assert all(e in F.edges and G.parent[e]==F.parent[e] for e in Cprime)
 assert canon(G.cut(Cprime))==canon(F.cut(Kprime)) and exact_yield(G.cut(Cprime),F.cut(Kprime))
 assert frag(G,Cprime,x)==frag(F,Kprime,x) and frag(G,Cprime,u)==frag(F,Kprime,u)
 assert descendant_frag(G,Cprime,x)==descendant_frag(F,Kprime,x) and descendant_frag(G,Cprime,u)==descendant_frag(F,Kprime,u)
 assert len(Kprime)==2+len(Cprime)
 return {'F':F.json(),'G':G.json(),'a':a,'c':c,'x':x,'u':u,'v':v,'B':sorted(B),'P':sorted(P),'K':sorted(K),'C':sorted(C),'Cprime':sorted(Cprime),'Kprime':sorted(Kprime),'second_parent_edge':pe,'unchanged_edges':sorted(S['unchanged']),'altered_corridor_edges':S['altered'],'old_fragments':{'x':frag(F,K,x),'u':frag(F,K,u)},'new_fragments':{'x':frag(F,Kprime,x),'u':frag(F,Kprime,u)},'counts':[len(K),len(C),len(Cprime),len(Kprime)],'yielded_equal':True,'exact_yielded_node_ids_and_parents_equal':True,'fragment_equal':True,'descendant_fragment_equal':True}

def controls():
 began=time.perf_counter();prior=old.controls();spec=json.loads((HERE/'two-stage-original-spec-frozen.json').read_text());T1=Graph.tree(spec['t1']);T2=Graph.tree(spec['t2']);a,c=(T2.bylabel[z] for z in spec['pair']);x=T2.bylabel[spec['uncle']];S=structural(T2,a,c,x);B=S['B'];rows=[]
 optimum=min(len(E) for E in old.powers(T2.edges) if old.af(T2.cut(E),T1,T2));assert optimum==2
 for names in spec['positive_cutsets']:
  E=frozenset(T2.bylabel[z] for z in names);assert old.af(T2.cut(E),T1,T2)
  K,_,_,_=old.normalization(T2,a,c,E|B);row=check_transport(T2,a,c,x,K)
  assert old.af(T2.cut(K),T1,T2) and old.af(T2.cut(row['Kprime']),T1,T2)
  assert [len(E),len(K),len(row['Kprime'])]==[2,3,2]
  assert frozenset(row['Kprime'])==B
  row['initial_E']=sorted(E);row['two_stage_counts']=[2,3,2];rows.append(row)
 for b in B:assert not old.af(T2.cut(B-{b}),T1,T2)
 corrupt=S['altered'][0];assert not(corrupt['after_present'] and corrupt['before_parent']==corrupt['after_parent'])
 v=S['v'];assert T2.parent[v] is not None
 F2=T2.cut({v}).yielded_graph();root1=next(w for w,p in T1.parent.items() if p==0);F1=T1.cut({root1}).yielded_graph()
 rootrows=[check_transport(F2,a,c,x,B|C) for C in old.powers(F2.edges-(B|S['P']))]
 assert all(r['second_parent_edge'] is None for r in rootrows)
 assert old.af(F2.cut(B),F1,F2)
 result={'status':'CONTROLS-PASS','oracle_controls':prior['status'],'oracle_reuse':str(EDGE/'adversary.py'),'oracle_sha256':hashlib.sha256((EDGE/'adversary.py').read_bytes()).hexdigest(),'optimum':optimum,'two_stage_controls':rows,'map_corruption_rejected':corrupt,'detached_rho':{'F1':F1.json(),'F2':F2.json(),'transport_cases':len(rootrows),'first':rootrows[0],'last':rootrows[-1]},'elapsed_seconds':time.perf_counter()-began}
 old.atomic(RESULTS/'thesis-correctness-repair-edge-second-controls.json',result)
 print(json.dumps({'status':result['status'],'optimum':optimum,'two_stage_cases':len(rows),'detached_rho_transport_cases':len(rootrows),'map_corruption_rejected':True,'elapsed_seconds':result['elapsed_seconds']}),flush=True)
 return result
if __name__=='__main__':controls()
