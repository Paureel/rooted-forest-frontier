"""One-shot joint ownership development wrapper; X0 is burned for certification.

Toolkit and existing instrument guides were consulted. The only new capability
is a lazy Lemma1-style cut-core generator and its ownership product. Exact
partition optima below are test queries, never candidate algorithm steps.
"""
from pathlib import Path
import sys
import json
import hashlib
import time
from fractions import Fraction
from itertools import product

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE.parent / "x0"))
from fresh_oracle import Tree, exact, validate_partition, applicability, tidy, forest_to_reference
from run_x0 import controls as x0_controls


def normalized_blocks(blocks):
    return sorted([sorted(c) for c in blocks], key=lambda c: (min(c), len(c)))


def core(tree, y):
    """Lazy source Lemma1 construction, using original edge IDs and label cuts.

    Work on a connected undirected tree, pruning each detached pure twig.
    Degree2 unlabeled vertices can remain: base detection checks edge sides.
    Recursive child creation is polynomial and incurs one paid source edge.
    """
    labels = {v: x for x, v in tree.leaf.items()}
    graph = {v: set() for v in tree.child}
    for u, v in tree.edges:
        graph[u].add(v)
        graph[v].add(u)
    original_edge = {frozenset((u,v)): (u,v) for u,v in tree.edges}
    def side(g, u, v):
        todo, used = [v], {u}
        while todo:
            w = todo.pop()
            if w in used:
                continue
            used.add(w)
            todo.extend(g[w] - used)
        used.remove(u)
        return used
    def descend(g, paid):
        live = {labels[v] for v in g if v in labels}
        yy, zz = live & set(y), live - set(y)
        assert yy and zz
        splits = []
        for u in sorted(g):
            for v in sorted(g[u]):
                if u > v:
                    continue
                region = side(g,u,v)
                s = {labels[w] for w in region if w in labels}
                if s == yy or s == zz:
                    splits.append(original_edge[frozenset((u,v))])
        if splits:
            yield tuple(sorted((*paid, min(splits))))
            return
        for u in sorted(g):
            if len(g[u]) != 3:
                continue
            regions = [(v,side(g,u,v)) for v in sorted(g[u])]
            pure_y = [(v,s) for v,s in regions if {labels[w] for w in s if w in labels} <= yy]
            pure_z = [(v,s) for v,s in regions if {labels[w] for w in s if w in labels} <= zz]
            mixed = [(v,s) for v,s in regions if {labels[w] for w in s if w in labels} & yy
                     and {labels[w] for w in s if w in labels} & zz]
            if pure_y and pure_z and mixed:
                for v,removed in (pure_y[0],pure_z[0]):
                    smaller = {w: adj - removed for w,adj in g.items() if w not in removed}
                    yield from descend(smaller, (*paid,original_edge[frozenset((u,v))]))
                return
        raise AssertionError("Lemma1 core construction has no pure-Y/pure-Z/mixed node")
    assert set(y) < set(tree.labels) and set(y)
    yield from descend(graph, ())


def span_edges(t, block):
    vertices = t.span(block)
    return {e for e in t.edges if set(e) <= vertices}


def ownership_product(t, forest, edge):
    """Actual algorithmic cut cover; no optimum query is used here."""
    far = t.below[edge[1]]
    trees = [Tree(raw) for raw in forest]
    cores = [list(core(f, f.labels & far)) for f in trees]
    for survivor in range(3):
        other = [i for i in range(3) if i != survivor]
        for left,right in product(cores[other[0]],cores[other[1]]):
            cuts = {other[0]: left, other[1]: right}
            blocks = []
            for i,f in enumerate(trees):
                if i == survivor:
                    blocks.append(sorted(f.labels))
                else:
                    pieces,empty = f.cut_blocks(cuts[i])
                    assert not empty, (i,cuts[i],empty)
                    blocks += pieces
            yield {'survivor':survivor,'cuts_by_source':cuts,
                   'paid':len(left)+len(right),'blocks':normalized_blocks(blocks)}


def source_controls():
    spec = json.loads((HERE.parent/'x0/source-control-spec-v1.json').read_text())
    rows=[]
    for c in spec['cases']:
        row=next(r for r in applicability(Tree(c['T']),Tree(c['Tprime']))['rows']
                 if r['cherry']==c['cherry'])
        assert all(row[k]==v for k,v in c['expected'].items())
        rows.append({'name':c['name'],'expected':c['expected'],'observed':row,'pass':True})
    return rows


def controls():
    inherited=x0_controls()
    src=source_controls()
    rows=[]
    f=Tree([0,1]); out=list(core(f,{0}))
    assert len(out)==1 and len(out[0])==1
    rows.append({'name':'single two-leaf split','cuts':out,'pass':True})
    f=Tree([[0,1],[2,3]]); out=list(core(f,{0,2}))
    assert len(out)==2 and all(len(c)==2 for c in out)
    mass=sum(Fraction(1,2)**len(c) for c in out)
    assert mass==Fraction(1,2)
    # Check all edge subsets that split colors are partition refinements of core.
    from itertools import combinations
    covered=0
    for n in range(len(f.edges)+1):
        for cut in combinations(f.edges,n):
            blocks,_=f.cut_blocks(cut)
            if any(set(b)&{0,2} and set(b)&{1,3} for b in blocks):
                continue
            assert any(all(any(set(b)<=set(c) for c in f.cut_blocks(k)[0]) for b in blocks) for k in out)
            covered+=1
    rows.append({'name':'mixed quartet core coverage','cuts':out,'mass2':str(mass),
                 'all_split_edge_subsets_covered':covered,'pass':True})
    # Abstract survivor omission has a concrete target refining only alternative2.
    ft=[[0,3],[1,4],[2,5]]
    t=Tree([[[0,1],2],[[3,4],5]])
    emitted=list(ownership_product(t,ft,('','0')))
    target=[[0],[3],[1],[4],[2,5]]
    survived=[r['survivor'] for r in emitted if all(any(set(b)<=set(c) for c in r['blocks']) for b in target)]
    assert survived==[2] and not any(i in [0,1] for i in survived)
    rows.append({'name':'missing survivor caught','target_partition':target,
                 'surviving_alternatives':survived,'bad_nonempty_cover':[0,1],'pass':True})
    bad=sum(Fraction(100,231)**d for d in [1,2,2])
    good=sum(Fraction(100,231)**d for d in [2,2,2])
    badfull=2*Fraction(100,231)+Fraction(100,231)**2*bad
    goodfull=2*Fraction(100,231)+Fraction(100,231)**2*good
    assert badfull>1 and goodfull<1
    rows.append({'name':'false residual recurrence caught','bad_mass':str(bad),
                 'good_mass':str(good),'bad_full_mass':str(badfull),
                 'good_full_mass':str(goodfull),'pass':True})
    return {'x0':inherited,'source_predicates':src,'product_controls':rows,
            'passed':inherited['passed']+len(src)+len(rows),
            'total':inherited['total']+len(src)+len(rows)}


def fixture(raw, other, cherry):
    started=time.perf_counter()
    a,b=Tree(raw),Tree(other)
    forward,reverse=applicability(a,b),applicability(b,a)
    out={'T':raw,'Tprime':other,'cherry':cherry,'source_checks':{'forward':forward,'reverse':reverse}}
    admitted=forward['excluded_2a_to_2d'] and reverse['excluded_2a_to_2d']
    out['parent_admitted']=admitted
    if not admitted:
        out['elapsed_seconds']=time.perf_counter()-started
        return out
    row=next(r for r in forward['rows'] if r['cherry']==cherry)
    edges=[p['edge'] for p in row['pendants']]
    blocks,empty=b.cut_blocks(edges)
    assert len(edges)==2 and len(blocks)==3 and not empty
    forest=[b.restriction(c) for c in blocks]
    reduced=tidy(raw,forest)
    tx=Tree(reduced['T']); rf=reduced['forest_trees']
    reference=forest_to_reference(tx,rf)
    rawopt=exact(a,b,refinement=blocks)
    reducedopt=exact(tx,reference,refinement=reduced['forest_blocks'])
    residual=rawopt['components']-len(blocks)
    assert residual==reducedopt['components']-len(rf)
    rebuilt=[]
    for p in reducedopt['optimal_partitions']:
        pp=[sorted(z for label in c for z in reduced['expansion'][label]) for c in p]+reduced['closed_components']
        v=validate_partition(a,b,pp,blocks)
        assert v['valid'] and len(pp)==rawopt['components']
        rebuilt.append({'partition':pp,'validation':v})
    sets=[span_edges(tx,c) for c in reduced['forest_blocks']]
    overlap=[{'sources':[i,j],'edges':sorted(sets[i]&sets[j])}
             for i in range(len(sets)) for j in range(i) if sets[i]&sets[j]]
    common=set.intersection(*sets) if len(sets)==3 else set()
    out.update({'pendants':row['pendants'],'paid_before_macro':2,'raw_blocks':blocks,
                'raw_optimum':rawopt,'reduced':reduced,'reduced_optimum':reducedopt,
                'residual_optimum':residual,'reconstruction':rebuilt,'overlap':overlap,
                'three_live':len(rf)==3,'common_edges':sorted(common)})
    if common:
        emitted=list(ownership_product(tx,rf,min(common)))
        for e in emitted:
            query=exact(tx,reference,refinement=e['blocks'])
            e['test_only_child_optimum']=query
            e['further_residual']=query['components']-len(e['blocks'])
            e['total_residual']=e['paid']+e['further_residual']
        assert min(e['total_residual'] for e in emitted)==residual
        for p in reducedopt['optimal_partitions']:
            assert any(all(any(set(c)<=set(r) for r in e['blocks']) for c in p) for e in emitted)
        vector=[e['paid'] for e in emitted]
        out['joint_macro']={'children':emitted,'paid_vector':vector,
                            'residual_mass_at_target':str(sum(Fraction(100,231)**d for d in vector)),
                            'full_vector':[1,1,*[2+d for d in vector]],
                            'full_mass_at_target':str(2*Fraction(100,231)+sum(Fraction(100,231)**(2+d) for d in vector)),
                            'finite_optimum_cover_survives':True}
    out['elapsed_seconds']=time.perf_counter()-started
    return out


def main():
    started=time.perf_counter()
    controls_out=controls()
    assert controls_out['passed']==controls_out['total']==33
    pin=json.loads((HERE/'PRE-RUN-v1.json').read_text())
    out={'scope':'Development finite evidence only; all three universal milestones OPEN',
         'controls':controls_out,'fixture':fixture(pin['T'],pin['Tprime'],pin['cherry']),
         'code_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'pin_sha256':hashlib.sha256((HERE/'PRE-RUN-v1.json').read_bytes()).hexdigest(),
         'contact':'X0 code, fixtures, and measured values used in development; never independent certification',
         'elapsed_seconds':time.perf_counter()-started}
    path=ROOT/'results/algorithm-macro-joint-pilot-v1.json'
    path.write_text(json.dumps(out,indent=2)+'\n')
    print('PASS controls: 33 / 33')
    print('Parent admitted:',out['fixture']['parent_admitted'])
    print('Three live:',out['fixture'].get('three_live'))
    print('Joint vector:',out['fixture'].get('joint_macro',{}).get('full_vector'))
    print('Elapsed seconds:',out['elapsed_seconds'])


if __name__=='__main__':
    main()
