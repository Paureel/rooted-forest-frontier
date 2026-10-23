"""Problem-specific local lemma adversary using uncompressed edge deletion.
Imports reconstructed algorithm only to obtain test states. The reference
never calls Forest.cut/reduce/shape/parent or the partition oracle.
"""
import argparse, copy, itertools, json, time
from pathlib import Path
import algorithm
HERE=Path(__file__).resolve().parent
OUT=HERE.parent/'results'


def component_data(f, removed):
    adjacency={v:[] for v in f.child}
    for u,cs in f.child.items():
        for v in cs:
            if v not in removed: adjacency[u].append(v); adjacency[v].append(u)
    left=set(adjacency); comps=[]
    while left:
        todo=[min(left)]; seen=set()
        while todo:
            v=todo.pop()
            if v in seen: continue
            seen.add(v);todo.extend(adjacency[v])
        left-=seen
        block=frozenset(f.label[v] for v in seen if v in f.label)
        if block: comps.append(block)
    return comps


def info(f, block):
    parent={c:v for v,cs in f.child.items() for c in cs}
    atom={lab:v for v,lab in f.label.items()}
    paths=[]
    for x in block:
        cur=atom[x];p=[]
        while True:
            p.append(cur)
            if cur not in parent: break
            cur=parent[cur]
        paths.append(p)
    common=set(paths[0]).intersection(*map(set,paths[1:]))
    if not common: return None,None
    top=next(v for v in paths[0] if v in common)
    vertices=set()
    for p in paths:vertices.update(p[:p.index(top)+1])
    def restrict(v):
        children=[restrict(c) for c in f.child[v] if c in vertices]
        children.sort(key=repr)
        lab=f.label.get(v)
        lab=tuple(sorted(lab)) if lab in block else None
        if lab is None and len(children)==1:return children[0]
        return (lab,tuple(children))
    return restrict(top),vertices


def all_optimal_cuts(f1,f2):
    edges=sorted(c for cs in f2.child.values() for c in cs)
    cache={}
    def admissible(cuts):
        used=set()
        for b in component_data(f2,cuts):
            if b not in cache:
                s1,v1=info(f1,b);s2,v2=info(f2,b)
                cache[b]=(s1 is not None and s1==s2,v1)
            ok,vs=cache[b]
            if not ok or used&vs:return False
            used|=vs
        return True
    for d in range(len(edges)+1):
        sols=[]
        for e in itertools.combinations(edges,d):
            if admissible(set(e)):sols.append(frozenset(e))
        if sols:return d,sols
    raise AssertionError('all-singleton cutset missing')


def controls():
    spec=json.loads((HERE/'controls.json').read_text());rows=[]
    for x in spec['known_answers']:
        d,sol=all_optimal_cuts(algorithm.Forest.tree(x['t1']),algorithm.Forest.tree(x['t2']))
        if d!=x['optimum_cuts']:raise AssertionError((x['id'],d,x['optimum_cuts']))
        rows.append({'id':x['id'],'cuts':d,'optimal_cutsets':len(sol)})
    # Exact counterexample to standalone Lemma 6.3: two labels, no triples,
    # one target component, and a disconnected source with no cuttable edge.
    f1=algorithm.Forest({0:[],1:[]},{0:frozenset(['rho']),1:frozenset(['a'])},set())
    f2=algorithm.Forest({0:[1],1:[]},{0:frozenset(['rho']),1:frozenset(['a'])},set())
    block=frozenset(f2.label.values())
    s1,_=info(f1,block);s2,_=info(f2,block)
    assert s1 is None and s2 is not None
    return rows,{'labels':['rho','a'],'F1_edges':[],'F2_edges':[['rho','a']],
                 'compatible_triples':True,'no_target_component_overlap':True,
                 'F2_is_forest_of_F1':False,'reason':'two-label joined component is not contained in any F1 component',
                 'consumer_ruling':'6.4 and 6.5 compare to connected T1, so this witness is outside their use-sites'}


def collect(limit):
    samples=json.loads((OUT/'thesis-correctness-sweep-n6-limit3000-seed612.json').read_text())['branch_witnesses']
    snapshots=[];seen=set();old=algorithm.branches
    def wrapped(f1,f2,av,cv,a,c):
        case,opts=old(f1,f2,av,cv,a,c)
        bs,u=f2.pendants(a,c)
        if bs is not None and len(bs)==2 and len(snapshots)<limit:
            # Stable graph serialization, used only to avoid duplicate tests.
            key=repr((sorted((v,cs) for v,cs in f1.child.items()),sorted((v,sorted(l)) for v,l in f1.label.items()),
                      sorted((v,cs) for v,cs in f2.child.items()),sorted((v,sorted(l)) for v,l in f2.label.items()),a,c))
            if key not in seen:
                seen.add(key);snapshots.append((copy.deepcopy(f1),copy.deepcopy(f2),a,c,bs,case))
        return case,opts
    algorithm.branches=wrapped
    try:
        for x in samples.values():
            for q in range(x['oracle_cuts']+2):algorithm.decide(x['t1'],x['t2'],q)
    finally:algorithm.branches=old
    return snapshots


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=4);args=ap.parse_args()
    start=time.perf_counter();ctl,witness=controls()
    states=collect(args.limit);rows=[]
    for i,(f1,f2,a,c,bs,case) in enumerate(states):
        d,sols=all_optimal_cuts(f1,f2)
        pair_possible=any(all(b in e for b in bs) for e in sols)
        for endpoint in [a,c]:
            premises=[e for e in sols if endpoint in e and any(b in e for b in bs)]
            passed=not premises or pair_possible
            rows.append({'state':i,'case':case,'endpoint':sorted(f2.label[endpoint]),'d':d,
                         'optimal_cutsets':len(sols),'antecedent_witnesses':len(premises),
                         'pendant_pair_optimum_exists':pair_possible,'pass':passed})
            if not passed:raise AssertionError(rows[-1])
    report={'scope':'finite local exchange checks, no universal theorem','controls':ctl,'lemma63_counterexample':witness,
            'requested_states':args.limit,'distinct_states':len(states),'endpoint_checks':len(rows),'checks':rows,
            'seconds':time.perf_counter()-start,'pass':all(r['pass'] for r in rows)}
    path=OUT/f'thesis-correctness-local-exchange-limit{args.limit}.json';path.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['checks','controls','lemma63_counterexample']},indent=2))
if __name__=='__main__':main()
