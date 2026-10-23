#!/usr/bin/env python3
"""Independent whole-remainder exchange audit; one-campaign verifier.
Reconstructs the stated elimination rule, not the candidate implementation.
"""
import argparse, itertools, json, random, time, hashlib
from functools import lru_cache
from pathlib import Path
from independent_graph import Tree, all_trees, partitions, local_valid, pure, control_run

def forest_cases():
    for n in range(4,6):
        labels=tuple(chr(97+i) for i in range(n))
        for tt in all_trees(labels):
            t=Tree(tt)
            for blocks in partitions(labels):
                if not pure(t,blocks) or not any(t.hull(a)&t.hull(b) for a,b in itertools.combinations(blocks,2)): continue
                for shapes in itertools.product(*(tuple(all_trees(tuple(sorted(b)))) for b in blocks)):
                    yield tt,shapes
    # Explicit equal-root clique held alongside the entire n<=5 pool.
    yield ((('a','b'),'c'),(('d','e'),'f')),(('a','d'),('b','e'),('c','f'))

def check_case(tt,shapes,profile,counts):
    t=Tree(tt); sources=tuple(Tree(s) for s in shapes);n=len(sources)
    labels=tuple(frozenset(s.labels) for s in sources)
    choices=tuple(partitions(tuple(sorted(b))) for b in labels)
    hulls=tuple(t.hull(b) for b in labels);roots=tuple(t.root(b) for b in labels)
    assert pure(t,labels)
    def valid_choices(i,marks):
        return tuple(p for p in choices[i] if local_valid(sources[i],t,labels[i],p,marks))
    all_options=[valid_choices(i,profile[i]) for i in range(n)]
    optimum=100;count=0
    for combo in itertools.product(*all_options):
        flat=tuple(b for p in combo for b in p)
        if all(not(t.hull(a)&t.hull(b)) for a,b in itertools.combinations(flat,2)):
            optimum=min(optimum,len(flat)-n);count+=1
    assert count
    counts['exact_feasible_forests']+=count
    # All deepest-root choices and all local minimum witnesses are explored.
    @lru_cache(None)
    def recurse(active,marks):
        if not active: return ((0,()),)
        maxdepth=max(len(roots[i]) for i in active);outputs=[]
        for i in active:
            if len(roots[i])!=maxdepth: continue
            opts=valid_choices(i,marks[i]);mu=min(len(p)-1 for p in opts)
            avoid=valid_choices(i,marks[i]|{roots[i]})
            free=[p for p in avoid if len(p)-1==mu]
            chosen=free if free else [p for p in opts if len(p)-1==mu]
            updated=list(marks)
            if not free:
                for j in active:
                    if i!=j and hulls[i]&hulls[j]: updated[j]=marks[j]|{roots[i]}
            remaining=tuple(j for j in active if j!=i)
            for p in chosen:
                for cost,fixed in recurse(remaining,tuple(updated)):
                    outputs.append((mu+cost,((i,p),)+fixed))
                    counts['elimination_nodes']+=1
        return tuple(outputs)
    outcomes=recurse(tuple(range(n)),tuple(profile))
    for cost,witness in outcomes:
        flat=tuple(b for i,p in witness for b in p)
        assert all(local_valid(sources[i],t,labels[i],p,profile[i]) for i,p in witness)
        assert all(not(t.hull(a)&t.hull(b)) for a,b in itertools.combinations(flat,2))
        assert cost==optimum,(tt,shapes,profile,cost,optimum,witness)
        counts['all_tie_elimination_outputs']+=1
    counts['profiles']+=1

def run(limit):
    start=time.perf_counter();controls=control_run();pool=list(forest_cases());random.Random(714).shuffle(pool)
    counts={'pool_cases':len(pool),'cases':0,'profiles':0,'exact_feasible_forests':0,'elimination_nodes':0,'all_tie_elimination_outputs':0}
    rng=random.Random(831);windows=[]
    for tt,shapes in pool[:limit]:
        t=Tree(tt);internal=tuple(t.children)
        no_marks=tuple(frozenset() for s in shapes)
        old_marks=tuple(frozenset(v for v in internal if rng.randrange(2)) for s in shapes)
        check_case(tt,shapes,no_marks,counts)
        check_case(tt,shapes,old_marks,counts)
        counts['cases']+=1
        if counts['cases']%32==0: windows.append({'cases':counts['cases'],'seconds':time.perf_counter()-start})
    return {'status':'finite-no-fire','counts':counts,'seconds':time.perf_counter()-start,'windows':windows,
       'controls_passed':controls['control_count'],'plants_caught':len(controls['caught_plants']),
       'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
       'scope':'All rooted target trees with 4 or 5 leaves, all pure nontrivially overlapping leaf partitions and source topologies; one explicit 6-leaf clique. Two initial mark profiles per case, all deepest ties and local minimum witnesses. Shares independent_graph core, not original candidate code.'}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--limit',type=int,default=32);p.add_argument('--output',required=True)
    a=p.parse_args();r=run(a.limit);Path(a.output).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
