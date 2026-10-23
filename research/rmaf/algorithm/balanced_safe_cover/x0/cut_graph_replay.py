#!/usr/bin/env python3
"""One-shot separate exact cut-graph replay of the X0 witness.
Does not import or call exact_x0; topology comes from pruned cut components.
"""
import argparse
from collections import defaultdict
from datetime import datetime, timezone
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import time


def assemble(data):
    adjacency, children, parent, labels = {}, {}, {}, {}
    serial = 0
    def node(x):
        nonlocal serial
        v = serial
        serial += 1
        adjacency[v] = set()
        if isinstance(x, str):
            labels[v] = x
            children[v] = []
        else:
            children[v] = [node(y) for y in x]
            for c in children[v]:
                adjacency[v].add(c); adjacency[c].add(v); parent[c] = v
        return v
    root = node(data)
    edges = tuple((p,c) for c,p in parent.items())
    return adjacency, children, parent, labels, edges, root


def resulting_forest(graph, cut):
    adj, child, par, lab, edges, root = graph
    banned = set(cut)
    unknown = set(adj)
    parts = {}
    while unknown:
        stack, component = [min(unknown)], set()
        while stack:
            v = stack.pop()
            if v in component:
                continue
            component.add(v)
            for w in adj[v]:
                e = (v,w) if par.get(w) == v else (w,v)
                if e not in banned:
                    stack.append(w)
        unknown -= component
        names = tuple(sorted(lab[v] for v in component if v in lab))
        if not names:
            return None
        roots = [v for v in component if par.get(v) not in component]
        if len(roots) != 1:
            raise AssertionError('cut component not rooted')
        def rooted(v):
            if v in lab:
                return ('leaf',lab[v])
            branches = [rooted(c) for c in child[v] if c in component]
            branches = [b for b in branches if b is not None]
            if not branches:
                return None
            if len(branches) == 1:
                return branches[0]
            return ('fork',) + tuple(sorted(branches,key=repr))
        parts[names] = rooted(roots[0])
    return parts


def all_cut_forests(graph, q):
    groups = defaultdict(list)
    for cut in combinations(graph[4], q):
        f = resulting_forest(graph,cut)
        if f is not None:
            key = tuple(sorted((names,topo) for names,topo in f.items()))
            groups[key].append(cut)
    return groups


def readable_partition(key):
    return [list(names) for names,_ in key]


def replay(inp,out):
    started = time.perf_counter()
    raw = inp.read_bytes()
    witness = json.loads(raw)['witness']
    source, target = assemble(witness['source']), assemble(witness['target'])
    n = witness['n']
    levels = []
    optima = None
    for q in range(n):
        sf,tf = all_cut_forests(source,q),all_cut_forests(target,q)
        joint = sorted(set(sf)&set(tf),key=repr)
        levels.append({'cuts':q,'source_distinct_valid_cut_forests':len(sf),'target_distinct_valid_cut_forests':len(tf),
                       'agreement_partitions':[readable_partition(k) for k in joint],
                       'source_cut_realization_counts':[len(sf[k]) for k in joint],
                       'target_cut_realization_counts':[len(tf[k]) for k in joint]})
        if joint and optima is None:
            optima = joint
            b = q
    proposed = tuple(sorted(tuple(x) for x in witness['exact']['precut_blocks']))
    def finer(key):
        return all(any(set(names)<=set(c) for c in proposed) for names,_ in key)
    surviving = [readable_partition(k) for k in optima if finer(k)]
    first_completion_total = next(row['cuts'] for row in levels if any(all(any(set(block)<=set(c) for c in proposed) for block in p) for p in row['agreement_partitions']))
    pre = []
    for cut in combinations(source[4],len(proposed)-1):
        f=resulting_forest(source,cut)
        if f is not None and tuple(sorted(f)) == proposed:
            pre.append(cut)
    checks = {'original_optimum_cuts':b == witness['exact']['optimum_cuts'],
              'original_optimum_partitions':sorted(readable_partition(k) for k in optima) == sorted(witness['exact']['optimum_partitions']),
              'surviving_count':len(surviving)==witness['exact']['surviving_optimum_count'],
              'completion_total':first_completion_total==witness['exact']['charged_total'],
              'distinct_precut_realizations':len(pre)==witness['exact']['distinct_precut_realization_count']}
    receipt={'kind':'separate-literal-cut-graph-replay','started_input_sha256':sha256(raw).hexdigest(),
             'script_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'utc':datetime.now(timezone.utc).isoformat(),
             'lineage':'no exact_x0 imports; independently built directed graph; cut source and target edges then prune and suppress components',
             'shared_layer':'labelled nested tree input, specified mathematical model, standard Python only',
             'source':witness['source'],'target':witness['target'],'levels':levels,
             'original_optimum_cuts':b,'original_optimum_partitions':[readable_partition(k) for k in optima],
             'precut_blocks':[list(p) for p in proposed], 'distinct_source_precut_realizations':pre,
             'surviving_optimum_partitions':surviving,'charged_total':first_completion_total,
             'checks':checks,'seconds':time.perf_counter()-started,
             'verdict':'REPRODUCES-WITNESS' if all(checks.values()) else 'WITNESS-MISMATCH'}
    out.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'verdict':receipt['verdict'],'checks':checks,'seconds':receipt['seconds']}))
    return all(checks.values())


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--input',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();raise SystemExit(0 if replay(a.input,a.out) else 1)
