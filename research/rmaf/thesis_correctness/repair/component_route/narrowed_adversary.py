#!/usr/bin/env python3
"""One-shot narrowed-target falsifier; imports only this route's own evaluator."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import random
import time
from evaluator import (Forest, ROUTE, RESULTS, atomic, all_subsets, all_trees,
                       af, contained, inspect_case, replay_controls, side_edges,
                       sibling_pair, normalized, compound_hunt)


def connected_labels(f, cuts, v):
    keep = set(f.children)
    component = {v}
    todo = [v]
    while todo:
        w = todo.pop()
        neighbors = [c for c in f.children[w] if c not in cuts]
        if w in f.parent and w not in cuts:
            neighbors.append(f.parent[w])
        for z in neighbors:
            if z not in component:
                component.add(z)
                todo.append(z)
    return frozenset(f.label[w] for w in component if w in f.label)


def fragments(f, cuts, a, c):
    A, C = f.desc(a), f.desc(c)
    u, pe, _ = f.path(a, c)
    removed = cuts & pe
    sa = connected_labels(f, cuts, a) & A
    sc = connected_labels(f, cuts, c) & C
    at_u = connected_labels(f, cuts, u)
    detached = (sa if not (sa & at_u) else frozenset()) | (sc if not (sc & at_u) else frozenset())
    anchor = (len(removed) != 1 or not (at_u - A - C) or not detached or bool(at_u & (A | C)))
    return {'S_a': sorted(sa), 'S_c': sorted(sc), 'at_u': sorted(at_u),
            'outside_at_u': sorted(at_u - A - C), 'detached_endpoint_labels': sorted(detached),
            'both_survive': bool(sa) and bool(sc), 'anchor_survives': anchor,
            'path_cut_count': len(removed)}


def empty_repairs(g1, g2, cuts):
    rows = []
    for v in sorted(g2.edges):
        A = g2.desc(v)
        if len(A) < 2:
            continue
        try:
            w = g1.node(A)
        except AssertionError:
            continue
        if g1.signature(w) != g2.signature(v):
            continue
        if connected_labels(g2, cuts, v) & A:
            continue
        internal = frozenset(e for e in cuts if e != v and g2.desc(e) < A)
        repaired = (cuts - internal) | {v}
        result = af(g2.yielded(repaired), g1, g2)
        rows.append({'A': sorted(A), 'internal_cuts': g2.edge_clusters(internal),
                     'old_cost': len(cuts), 'new_cost': len(repaired),
                     'new_cuts': g2.edge_clusters(repaired), 'AF': result,
                     'two_internal_cuts': len(internal) >= 2,
                     'strict_cost': len(repaired) < len(cuts)})
    return rows


def narrowed_controls():
    replay_controls()
    c = ['c1', 'c2']
    t1 = Forest.tree([[['a', c], 'b'], 'd'])
    t2 = Forest.tree([['a', c], ['b', 'd']])
    cuts = t2.edge_ids([['a'], ['c1'], ['c2']])
    frag = fragments(t2, cuts, t2.node('a'), t2.node(c))
    assert frag['both_survive'] is False and frag['anchor_survives'] is False
    repairs = empty_repairs(t1, t2, cuts)
    c_repair = next(x for x in repairs if x['A'] == c)
    assert c_repair['new_cost'] == 2 and c_repair['AF']['ok'] and c_repair['two_internal_cuts']
    # A concrete faulty repair, unlike merely corrupting an expected Boolean:
    # undoing internal cuts without detaching the restored common subtree fails.
    faulty = cuts - t2.edge_ids([['c1'], ['c2']])
    assert af(t2.yielded(faulty), t1, t2)['ok'] is False
    optima = []
    for e in all_subsets(t2.edges):
        if optima and len(e) > len(optima[0]):
            break
        if af(t2.yielded(e), t1, t2)['ok']:
            optima.append(e)
    assert len(optima[0]) == 1
    assert all(connected_labels(t2, e, t2.node(c)) & frozenset(c) for e in optima)
    clean = Forest.tree([['a', c], ['b', 'd']])
    e = clean.edge_ids([['a'], c])
    good = fragments(clean, e, clean.node('a'), clean.node(c))
    assert good['both_survive'] and good['anchor_survives']
    nn, _ = normalized(clean, e, clean.node('a'), clean.node(c))
    assert af(clean.yielded(nn), clean, clean)['ok']
    return {'compound_tombstone_excluded': True, 'explicit_bad_repair_caught': True,
            'empty_subtree_repair': c_repair, 'compound_minimum_cost': 1,
            'minimum_sets_count': len(optima), 'minimum_subtree_survival': True,
            'positive_compound_normalization': True}


def search(n, limit, seed):
    labels = tuple('abcde'[:n])
    trees = all_trees(labels)
    pairs = [(a,b) for a in trees for b in trees]
    random.Random(seed).shuffle(pairs)
    stats = {'tree_pairs_started': 0, 'AF_cutsets': 0, 'common_sibling_AF_premises': 0,
             'both_survive_premises': 0, 'anchor_survives_premises': 0,
             'compound_sibling_AF_premises': 0, 'root_boundary_premises': 0,
             'empty_subtree_repairs': 0}
    failures, rows, timing = [], [], []
    start = time.perf_counter()
    for one,two in pairs:
        stats['tree_pairs_started'] += 1
        t1,t2 = Forest.tree(one),Forest.tree(two)
        for detached in (False,True):
            g2 = t2.yielded({t2.children[0][0]}) if detached else t2
            for f1_detached in ((False,True) if detached else (False,)):
                g1 = t1.yielded({t1.children[0][0]}) if f1_detached else t1
                assert contained(g2,g1)
                siblings = []
                for cs in g1.children.values():
                    if len(cs) != 2:
                        continue
                    A,C = [g1.desc(v) for v in cs]
                    try:
                        a,c = g2.node(A),g2.node(C)
                    except AssertionError:
                        continue
                    if g1.signature(cs[0]) != g2.signature(a) or g1.signature(cs[1]) != g2.signature(c):
                        continue
                    if g2.path(a,c) is None:
                        continue
                    sides = side_edges(g2,a,c)
                    if sibling_pair(g1,g2.yielded(sides),A,C):
                        siblings.append((A,C,a,c,sides))
                if not siblings:
                    continue
                for cuts in all_subsets(g2.edges):
                    if not af(g2.yielded(cuts),g1,g2)['ok']:
                        continue
                    stats['AF_cutsets'] += 1
                    for repair in empty_repairs(g1,g2,cuts):
                        stats['empty_subtree_repairs'] += 1
                        if not (repair['two_internal_cuts'] and repair['strict_cost'] and repair['AF']['ok']):
                            failures.append({'kind':'empty_repair','T1':one,'T2':two,
                                             'cuts':g2.edge_clusters(cuts),'repair':repair})
                    for A,C,a,c,sides in siblings:
                        if not sides <= cuts:
                            continue
                        stats['common_sibling_AF_premises'] += 1
                        frag = fragments(g2,cuts,a,c)
                        if len(A)>1 or len(C)>1:
                            stats['compound_sibling_AF_premises'] += 1
                        u,pe,_ = g2.path(a,c)
                        if u not in g2.parent and len(cuts&pe)>=2:
                            stats['root_boundary_premises'] += 1
                        new,info = normalized(g2,cuts,a,c)
                        agrees = af(g2.yielded(new),g1,g2)['ok']
                        for key in ('both_survive','anchor_survives'):
                            if frag[key]:
                                stats[key+'_premises'] += 1
                                if not agrees:
                                    failures.append({'kind':key,'T1':one,'T2':two,
                                        'F1_root_detached':f1_detached,'F2_root_detached':detached,
                                        'pair':[sorted(A),sorted(C)],'cuts':g2.edge_clusters(cuts),
                                        'new_cuts':g2.edge_clusters(new),'fragments':frag})
                        if len(rows)<4 and (len(A)>1 or len(C)>1) and frag['anchor_survives']:
                            rows.append({'T1':one,'T2':two,'pair':[sorted(A),sorted(C)],
                                         'cuts':g2.edge_clusters(cuts),'fragments':frag,'AF_after':agrees})
                    if stats['AF_cutsets'] % 100 == 0:
                        timing.append({'AF_cutsets':stats['AF_cutsets'],'seconds':time.perf_counter()-start})
                    if limit and stats['AF_cutsets']>=limit:
                        return {'stats':stats,'failures':failures,'compound_examples':rows,
                                'timings':timing,'seconds':time.perf_counter()-start,'exhaustive':False}
    return {'stats':stats,'failures':failures,'compound_examples':rows,
            'timings':timing,'seconds':time.perf_counter()-start,'exhaustive':True}


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--n',type=int,default=4)
    p.add_argument('--limit',type=int,default=500)
    p.add_argument('--seed',type=int,default=6510)
    p.add_argument('--name',default='narrowed-pilot')
    args=p.parse_args()
    control=narrowed_controls()
    result={'timestamp':datetime.now(timezone.utc).isoformat(),'n':args.n,'limit':args.limit,
            'seed':args.seed,'controls':control,'target_sha256':hashlib.sha256((ROUTE/'PROOF-TARGET.md').read_bytes()).hexdigest(),
            'search':search(args.n,args.limit,args.seed)}
    path=RESULTS/('thesis-correctness-repair-component-'+args.name+'.json')
    atomic(path,result)
    print(json.dumps({'receipt':str(path),**result['search']['stats'],
                      'failures':len(result['search']['failures']),
                      'seconds':result['search']['seconds'],'exhaustive':result['search']['exhaustive']},sort_keys=True))
    assert not result['search']['failures']

if __name__=='__main__':
    main()
