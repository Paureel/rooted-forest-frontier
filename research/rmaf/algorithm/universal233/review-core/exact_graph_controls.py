#!/usr/bin/env python3
# One-shot independent rooted graph review. No production/author imports.
# Shared SPEC only: binary rooted trees with Nat leaf labels and child addresses.
from pathlib import Path
from functools import lru_cache
from itertools import product
import argparse, hashlib, json, time
D=Path(__file__).resolve().parent

def graph(t):
    vertices=set(); edges=set(); leaves={}; cherries=[]
    def walk(s,p):
        vertices.add(p)
        if isinstance(s,int): leaves[p]=s; return
        if all(isinstance(v,int) for v in s): cherries.append(p)
        for k,child in enumerate(s):
            q=p+(k,); edges.add((p,q)); walk(child,q)
    walk(t,())
    nbr={v:set() for v in vertices}
    for a,b in edges: nbr[a].add(b); nbr[b].add(a)
    return vertices,edges,leaves,cherries,nbr

def connected(s,nbr):
    if not s:return True
    reached={next(iter(s))};todo=list(reached)
    while todo:
        for w in nbr[todo.pop()] & s - reached: reached.add(w);todo.append(w)
    return reached==s

def valid(G,owners,supports):
    vertices,edges,leaves,cherries,nbr=G
    seen=set()
    for i,s in supports.items():
        if not s<=vertices or seen&s or not connected(s,nbr):return False
        if any((v in s)!=(owners[v]==i) for v in leaves):return False
        seen |= s
    return all(v in supports.get(i,set()) for v,i in owners.items())

def surgery(G,owners,supports,p,remove_other=True):
    a,b=owners[p+(0,)],owners[p+(1,)]
    if a==b:return dict(owners),{i:set(s) for i,s in supports.items()}
    qo={v:(a if i==b else i) for v,i in owners.items()}
    qs={i:set(s) for i,s in supports.items()}
    qs[a]=qs.get(a,set())|qs.get(b,set())|{p};qs[b]=set()
    if remove_other:
        for i in qs:
            if i not in (a,b):qs[i].discard(p)
    return qo,qs

def refined(po,qo):
    return all(po[u]!=po[v] or qo[u]==qo[v] for u in po for v in po)

def monochrome(owners,colors):
    return all(owners[u]!=owners[v] or colors[u]==colors[v] for u in owners for v in owners)

def demand(cond,msg):
    if not cond:raise AssertionError(msg)

def expect_caught(name,fn):
    try:fn()
    except AssertionError:return {'name':name,'status':'CAUGHT'}
    raise AssertionError('Plant survived: '+name)

def controls():
    # Third block owns an irrelevant pendant excursion through cherry parent.
    t=((0,1),2);G=graph(t);p=(0,)
    owners={(0,0):0,(0,1):1,(1,):2}
    supports={0:{(0,0)},1:{(0,1)},2:{(),p,(1,)}}
    demand(valid(G,owners,supports),'positive third-block fixture')
    qo,qs=surgery(G,owners,supports,p)
    demand(qs[0]=={(0,0),(0,1),p} and qs[2]=={(),(1,)},'known surgery sets')
    demand(valid(G,qo,qs) and refined(owners,qo),'positive surgery')
    catches=[]
    bo,bs=surgery(G,owners,supports,p,False)
    catches.append(expect_caught('unchanged_third_parent',lambda:demand(valid(G,bo,bs),'overlap')))
    catches.append(expect_caught('exact_partition_preservation',lambda:demand(owners==qo,'coarsening changes owner relation')))
    overlap={i:set(s) for i,s in supports.items()};overlap[0].add(p)
    catches.append(expect_caught('overlap',lambda:demand(valid(G,owners,overlap),'overlap')))
    disconn={i:set(s) for i,s in supports.items()};disconn[2].remove(())
    catches.append(expect_caught('disconnected',lambda:demand(valid(G,owners,disconn),'disconnected')))
    foreign={i:set(s) for i,s in supports.items()};foreign[0].add((0,1))
    catches.append(expect_caught('foreign_terminal',lambda:demand(valid(G,owners,foreign),'terminal exact')))
    demand(refined(owners,owners),'refinement clean twin')
    catches.append(expect_caught('refinement_comparator',lambda:demand(refined(qo,owners),'split merged pair')))
    # SourcePartition permits supports with no terminals, including empty support after surgery.
    for t,p,s in [(((0,1),2),(0,),{(),(0,)}),((0,1),(),{()})]:
        g=graph(t);o={v:i for i,v in enumerate(g[2])};ss={i:{v} for v,i in o.items()};ss[99]=s
        demand(valid(g,o,ss),'leafless block fixture');oo,sss=surgery(g,o,ss,p)
        demand(valid(g,oo,sss) and refined(o,oo),'leafless block surgery')
    # Syntactic GoodCuts + OutputShape do not imply source edge realization.
    g=graph(((0,1),2));fakecuts=[(0,0,0)];fakepartition=[[0],[1,2]]
    syntactic=(len(set(fakecuts))==len(fakecuts) and all(fakecuts) and len(fakepartition)==len(fakecuts)+1)
    demand(syntactic,'syntactic-output clean witness')
    catches.append(expect_caught('syntactic_implies_realized_cuts',lambda:demand(all(v in g[0] for v in fakecuts),'nonexistent source endpoint')))
    # Addresses may all be actual and still leave a leafless component.
    actualcuts=[(0,),(1,)]
    rem=g[1]-{(v[:-1],v) for v in actualcuts};nbr={v:set() for v in g[0]}
    for u,v in rem:nbr[u].add(v);nbr[v].add(u)
    demand(not (nbr[()] & g[0]),'root isolated by two actual cuts')
    catches.append(expect_caught('nonredundancy_from_distinct_actual_cuts',lambda:demand(() in g[2] or nbr[()],'leafless residual root')))
    # Root and one-vertex boundary definitions.
    demand(len(graph(7)[0])==1 and not graph(7)[1],'singleton graph null')
    demand(graph((0,1))[3]==[()],'root cherry')
    return {'positive_fixtures':['third_block_partition_and_surgery','refinement_identity','leafless_pendant_support','leafless_root_support','fake_output_syntactic','actual_cuts_leafless_root','singleton_graph','root_cherry'],'plants':catches,'exact_misleading_witnesses':{
        'unchanged_third_parent':{'tree':[[0,1],2],'parent':[0],'old_supports':{'0':[[0,0]],'1':[[0,1]],'2':[[],[0],[1]]},'new_merged_support':[[0],[0,0],[0,1]],'wrong_third_support':[[],[0],[1]],'overlap':[[0]],'expected_disjoint':True,'actual_disjoint':False},
        'exact_partition_preservation':{'tree':[[0,1],2],'old_same_block_0_1':False,'new_same_block_0_1':True,'old_refines_new':True,'new_refines_old':False},
        'syntactic_implies_realized_cuts':{'tree':[[0,1],2],'partition':[[0],[1,2]],'cuts':[[0,0,0]],'GoodCuts':True,'OutputShape':True,'actual_endpoint':False},
        'nonredundancy_from_distinct_actual_cuts':{'tree':[[0,1],2],'cuts':[[0],[1]],'both_endpoints_actual':True,'root_residual_component':[[]],'root_component_leaf_labels':[]}
    }}

@lru_cache(None)
def shapes(n):
    if n==1:return (None,)
    return tuple((a,b) for k in range(1,n) for a in shapes(k) for b in shapes(n-k))

def label(shape):
    q=iter(range(100))
    def f(s):return next(q) if s is None else (f(s[0]),f(s[1]))
    return f(shape)

@lru_cache(None)
def rgs(n):
    if n==0:return ((),)
    if n==1:return ((0,),)
    return tuple(p+(i,) for p in rgs(n-1) for i in range(max(p)+2))

def census(n):
    start=time.monotonic();cnt={'n':n,'trees':0,'assignments':0,'valid_supports':0,'colorings':0,'mixed':0,'unique':0,'homogeneous':0,'third_parent':0,'root_cherry':0}
    for shape in shapes(n):
        G=graph(label(shape));vertices,edges,leaves,cherries,nbr=G;lv=tuple(leaves);iv=tuple(sorted(vertices-set(lv)));cnt['trees']+=1
        for po in rgs(n):
            owners=dict(zip(lv,po));b=max(po)+1
            bases={i:{v for v in lv if owners[v]==i} for i in range(b)}
            for a in product(range(-1,b),repeat=len(iv)):
                cnt['assignments']+=1
                ss={i:set(s) for i,s in bases.items()}
                for v,i in zip(iv,a):
                    if i>=0:ss[i].add(v)
                if not valid(G,owners,ss):continue
                cnt['valid_supports']+=1
                for bc in rgs(b):
                    colors={v:bc[owners[v]] for v in lv};cnt['colorings']+=1
                    demand(monochrome(owners,colors),'color generator')
                    for u in lv:
                        if sum(colors[u]==colors[v] for v in lv)==1:
                            cnt['unique']+=1;demand(sum(owners[u]==owners[v] for v in lv)==1,('unique',n,owners,ss,colors))
                    for p in cherries:
                        u,v=p+(0,),p+(1,)
                        if colors[u]!=colors[v]:
                            cnt['mixed']+=1
                            demand(sum(owners[u]==owners[w] for w in lv)==1 or sum(owners[v]==owners[w] for w in lv)==1,('mixed',n,owners,ss,colors))
                        else:
                            cnt['homogeneous']+=1
                            oo,s=surgery(G,owners,ss,p)
                            demand(valid(G,oo,s) and refined(owners,oo) and monochrome(oo,colors) and oo[u]==oo[v],('homogeneous',n,owners,ss,colors))
                            if owners[u]!=owners[v] and any(p in si for i,si in ss.items() if i not in (owners[u],owners[v])):cnt['third_parent']+=1
                            if not p:cnt['root_cherry']+=1
    cnt['seconds']=round(time.monotonic()-start,5)
    return cnt

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-n',type=int,default=4);args=ap.parse_args()
    result={'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'controls':controls(),'census':[],'status':'CONFIRMED','scope':'finite_controls_only'}
    for n in range(2,args.max_n+1):
        row=census(n);result['census'].append(row);print(json.dumps(row),flush=True)
    (D/('graph-controls-n'+str(args.max_n)+'.json')).write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: independent finite graph controls and deliberate plants; no universal inference',flush=True)
if __name__=='__main__':main()
