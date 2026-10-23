#!/usr/bin/env python3
"""One-campaign source-side transport and role-swap audit.
Uses this review's own graph engine; not independent of independent_graph.py.
"""
import argparse, hashlib, itertools, json, random, time
from pathlib import Path
from independent_graph import Tree, partitions, all_trees, local_valid, optimum, control_run

def region_valid(source, target, labels, partition, regions):
    # Rebuild the suppressed region trees with fresh addresses. This tests the
    # embedding-disjointness under suppression, not just label containment.
    used=set()
    for block in partition:
        hs=source.hull(block)
        if hs & used: return False
        used.update(hs)
        if not any(block<=r for r in regions): return False
    for region in regions:
        regtree=Tree(target.restriction(region))
        used=set()
        for block in partition:
            if not block<=region: continue
            if source.restriction(block)!=regtree.restriction(block): return False
            ht=regtree.hull(block)
            if ht & used: return False
            used.update(ht)
    return True

def cases():
    for n in range(2,6):
        labels=tuple(chr(97+i) for i in range(n))
        for target in all_trees(labels):
            for size in range(2,n+1):
                for selected in itertools.combinations(labels,size):
                    for source in all_trees(selected): yield source,target,selected

def run(limit, checkpoint=None):
    start=time.perf_counter(); controls=control_run()
    pool=list(cases()); random.Random(20261014).shuffle(pool)
    selected_cases=pool[:limit]; result={'case_pool':len(pool),'cases':0,'source_transport':0,
        'role_swap_families':0,'role_swap_partition_comparisons':0,'refined_optimal_forests':0,
        'empty_region_queries':0,'root_mark_queries':0,'region_counts':{},'max_residual':0}
    windows=[]
    for idx,(ss,tt,labels) in enumerate(selected_cases):
        s=Tree(ss);t=Tree(tt); labels=frozenset(labels); allp=partitions(tuple(sorted(labels)))
        d,ordinary=optimum(s,t,labels)
        for v in t.hull(labels)-set(t.labels.values()):
            if t.degree(labels,v)!=2: continue
            reg,_=t.regions([v])
            for size in range(1,len(labels)+1):
                for chosen in itertools.combinations(sorted(labels),size):
                    block=frozenset(chosen)
                    if v not in t.hull(block) or s.restriction(block)!=t.restriction(block): continue
                    split=tuple(block&r for r in reg if block&r)
                    oldmarks=set(t.children)-set(t.hull(block))
                    assert len(split)==2 and local_valid(s,t,block,split,oldmarks|{v}), (ss,tt,labels,v,block)
                    result['source_transport']+=1
        internal=tuple(t.children)
        for bits in itertools.product((0,1),repeat=len(internal)):
            marks={v for v,b in zip(internal,bits) if b}
            raw,empty=t.regions(marks)
            regions=tuple(r&labels for r in raw if r&labels)
            r=len(regions)
            marked=[p for p in allp if local_valid(s,t,labels,p,marks)]
            role=[p for p in allp if region_valid(s,t,labels,p,regions)]
            assert marked==role, (ss,tt,labels,marks,'partition-family-mismatch')
            h=min(len(p)-1 for p in marked)
            q=h-(r-1)
            assert 0<=q<=d and h<=d+r-1, (ss,tt,labels,marks,h,r,d)
            refinement=tuple(b&reg for b in ordinary for reg in regions if b&reg)
            assert local_valid(s,t,labels,refinement,marks)
            assert len(refinement)-len(ordinary)<=r-1
            result['role_swap_families']+=1
            result['role_swap_partition_comparisons']+=len(allp)
            result['refined_optimal_forests']+=1
            result['empty_region_queries']+=bool(empty or any(not(rg&labels) for rg in raw))
            result['root_mark_queries']+=() in marks
            result['region_counts'][r]=result['region_counts'].get(r,0)+1
            result['max_residual']=max(result['max_residual'],q)
        result['cases']+=1
        if (idx+1)%32==0:
            windows.append({'cases':idx+1,'seconds':time.perf_counter()-start})
            if checkpoint and (idx+1)%256==0:
                Path(checkpoint).write_text(json.dumps({'status':'running','counts':result,'last_window':windows[-1]},indent=2)+'\n')
    return {'status':'finite-no-fire','counts':result,'controls_passed':controls['control_count'],
        'plants_caught':len(controls['caught_plants']),'seconds':time.perf_counter()-start,'windows':windows,
        'sources':{p:hashlib.sha256(Path(__file__).with_name(p).read_bytes()).hexdigest()
            for p in ['local_interfaces.py','independent_graph.py']},
        'scope':'New author/BFS/partition code; source transport, suppressed-region family identity, role budget and optimal forest refinement share this review graph core. Finite checks, not universal proof.'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--limit',type=int,default=32);p.add_argument('--output',required=True)
    a=p.parse_args();r=run(a.limit,a.output+'.progress');Path(a.output).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
