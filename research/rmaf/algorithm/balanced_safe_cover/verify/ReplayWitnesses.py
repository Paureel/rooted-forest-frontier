#!/usr/bin/env python3
"""Independent post-freeze geometry/witness replay using only our original-edge engine."""
import hashlib,itertools,json,time
from pathlib import Path
from IndependentEdges import Raw,score,solve,blockkey,compare,agreement
HERE=Path(__file__).parent;ROOT=Path(__file__).resolve().parents[5]

def geometry(s,t,q):
    S,T=Raw(s),Raw(t);q=blockkey(q);spans=[T.support(b) for b in q];overlaps=[]
    for i,j in itertools.combinations(range(len(q)),2):
        for v in sorted(spans[i]&spans[j]):
            degrees=[sum(v in e and set(e)<=spans[k] for e in T.edges) for k in (i,j)]
            overlaps.append(dict(components=[i,j],vertex=v,degrees=degrees))
    return dict(pure_bridge=all(x['degrees']==[2,2] for x in overlaps),overlaps=overlaps,
                compatible_or_triple=all(len(b)==3 or S.restriction(b)==T.restriction(b) for b in q))

def raw_components(raw,deleted):
    graph={v:[] for v in raw.children}
    for u,v in raw.edges:
        if (u,v) not in deleted:graph[u].append(v);graph[v].append(u)
    remaining=set(graph);cs=[]
    while remaining:
        seed=min(remaining);stack=[seed];comp=set()
        while stack:
            v=stack.pop()
            if v in comp:continue
            comp.add(v);stack.extend(graph[v])
        remaining-=comp;cs.append(comp)
    return cs

def quotient(raw,K):
    cs=raw_components(raw,K);owner={v:i for i,c in enumerate(cs) for v in c};es=[(owner[u],owner[v]) for u,v in K]
    return dict(edges=es,degrees=[sum(i in e for e in es) for i in range(len(cs))],full_regions=[dict(vertices=sorted(c),labels=sorted(x for x,v in raw.leaf.items() if v in c)) for c in cs])

def run():
    reports=[]
    # Geometry controls before new witness reads.
    positive=geometry([['a','c'],['b','d']],[['a','b'],['c','d']],[['a','c'],['b','d']]);compare(positive['pure_bridge'],True,'pure_positive')
    corrupt=geometry([[['a','c'],'e'],['b','d']],[[['a','b'],['c','d']],'e'],[['a','c','e'],['b','d']]);compare(corrupt['pure_bridge'],False,'degree_three_corruption')
    s=[[[[['a','b'],'c'],'d'],'e'],'f'];t=[['a','c'],[['b','e'],['d','f']]]
    x=score(s,t);compare(x['optimum_cuts'],3,'n6.original_optimum')
    S,T,cuts,aps,best,opts=solve(s,t);K=[(S.parent[S.leaf[z]],S.leaf[z]) for z in 'bdf'];q=quotient(S,K)
    compare(sorted(q['degrees']),[1,1,1,3],'n6.star');compare(agreement(S,T,blockkey([v['labels'] for v in q['full_regions']])),True,'n6.K_agreement')
    opt_realizations=sum(len(cuts[p]) for p in opts);compare(opt_realizations,19,'n6.optimum_realizations')
    one=[];repairs=[]
    for z in 'bdf':
        r=score(s,t,[[z],list(S.labels-{z})]);compare(r['tau'],2,'n6.onecut.'+z)
        one.append(dict(isolated=z,**r,**geometry(s,t,r['precut_blocks']),failing_step='Q2-ONE balance after one star edge',lhs_tau=r['tau'],rhs_threshold=1,residual=r['tau']-1))
    for zs in itertools.combinations('bdf',2):
        r=score(s,t,[[z] for z in zs]+[list(S.labels-set(zs))]);compare(r['tau'],1,'n6.repair.tau');compare(r['charged_total'],3,'n6.repair.charge')
        g=geometry(s,t,r['precut_blocks']);compare(g['pure_bridge'],True,'n6.repair.purity');repairs.append(dict(isolated=list(zs),**r,**g))
    n6=dict(source=s,target=t,original=x,optimal_realization_count=opt_realizations,original_K=K,quotient=q,onecuts=one,twocut_repairs=repairs)
    s=[[['c',['a','b']],'d'],[['e','f'],'g']];t=[['a',[[['e',['c','d']],'f'],'g']],'b'];x=score(s,t);compare(x['optimum_cuts'],2,'n7.original_optimum')
    S,T,cuts,aps,best,opts=solve(s,t);Kblocks=blockkey([['a','b'],['c','d'],['e','f','g']]);compare(Kblocks in opts,True,'n7.K_original_optimum');compare(sum(len(cuts[p]) for p in opts),2,'n7.optimum_realizations')
    rows=[]
    for B,pure in [(['a','b'],True),(['e','f','g'],False)]:
        r=score(s,t,[B,list(S.labels-set(B))]);g=geometry(s,t,r['precut_blocks']);compare(g['pure_bridge'],pure,'n7.purity');compare(g['compatible_or_triple'],False,'n7.tripleclass');compare(r['tau'],1,'n7.tau');compare(r['one_optimum_survival'],True,'n7.survival')
        rows.append(dict(precut_subtree=B,**r,**g))
    n7=dict(source=s,target=t,original=x,K_blocks=Kblocks,K_actual_original_cuts=cuts[Kblocks],half_subset_rows=rows,failure=dict(failing_step='Q-HALF-ANY terminal class after cutting efg',pure_bridge=False,compatible_or_triple=False,impure_degree_witness=[x for x in rows[1]['overlaps'] if x['degrees']!=[2,2]],balanced_tau=1,threshold=1,residual_terminal_acceptance=False))
    # Re-evaluate terminal controls without any route predicates.
    mf=json.loads((HERE.parent/'FROZEN-CONTROLS.json').read_text());term=[]
    for f in mf['fixtures']:
        if 'source' not in f or 'expected_terminal' not in f:continue
        q=f.get('precut_blocks',[list(Raw(f['source']).labels)]);g=geometry(f['source'],f['target'],q)
        expected=g['pure_bridge'] if f['expected_terminal']=='pure-bridge' else g['compatible_or_triple'];compare(expected,True,f['id']+'.terminal');term.append(dict(id=f['id'],**g))
    product=json.loads((ROOT/'research/rmaf/results/algorithm-balanced-cover-verify-product-r2.json').read_text())['result']['cases'];pt=[]
    for r in product:
        g=geometry(r['source'],r['target'],r['precut_blocks']);compare(g['pure_bridge'],True,'product.purity');pt.append(dict(r=r['r'],**g))
    return dict(geometry_controls=dict(positive=positive,corruption=corrupt),terminal_fixture_checks=term,product_terminal_checks=pt,n6=n6,n7=n7,scope='ordinary unreduced raw trees; no reduction history or safe-cover nonexistence follows')

if __name__=='__main__':
    start=time.perf_counter();result=run();receipt=dict(source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),instrument_sha256=hashlib.sha256((HERE/'IndependentEdges.py').read_bytes()).hexdigest(),elapsed_seconds=time.perf_counter()-start,result=result);out=ROOT/'research/rmaf/results/algorithm-balanced-cover-verify-witnesses.json';out.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(dict(out=str(out),elapsed_seconds=receipt['elapsed_seconds'],n6_opt=result['n6']['original']['optimum_cuts'],n7_opt=result['n7']['original']['optimum_cuts'])))
