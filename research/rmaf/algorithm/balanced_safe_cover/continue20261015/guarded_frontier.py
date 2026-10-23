#!/usr/bin/env python3
"""One-shot CB4 paid guarded original-edge frontier; alpha bound OPEN."""
import itertools
import conflict_solver as core
import conflict_dag_solver as dag
import conflict_row_selector as selector


def components(S, cuts):
    adjacent = {v: [] for v in S.parent}
    for e, (u,v) in enumerate(S.edges):
        if not cuts & (1 << e):
            adjacent[u].append(v)
            adjacent[v].append(u)
    reverse = {v:a for a,v in S.leaf.items()}
    unseen, out = set(S.parent), []
    while unseen:
        first = min(unseen)
        todo, vertices = [first], set()
        unseen.remove(first)
        while todo:
            v = todo.pop()
            vertices.add(v)
            for w in adjacent[v]:
                if w in unseen:
                    unseen.remove(w)
                    todo.append(w)
        labels = tuple(sorted(reverse[v] for v in vertices if v in reverse))
        if not labels:
            return None
        out.append((labels, frozenset(vertices)))
    return sorted(out), adjacent


def witness(S, T, labels, vertices, adjacent):
    if S.restrict(labels) == T.restrict(labels):
        blocks = [tuple(labels)]
    else:
        used_labels, used_s, used_t, blocks = set(), set(), set(), []
        for a,b in itertools.combinations(labels,2):
            if a in used_labels or b in used_labels:
                continue
            ps, pt = S.support((a,b)), T.support((a,b))
            if not (used_s & ps or used_t & pt):
                blocks.append((a,b))
                used_labels.update((a,b))
                used_s.update(ps)
                used_t.update(pt)
        blocks += [(a,) for a in labels if a not in used_labels]
        blocks.sort()
    used_s, used_t = set(), set()
    owner = {}
    for index, block in enumerate(blocks):
        ss, st = S.support(block), T.support(block)
        if S.restrict(block) != T.restrict(block) or used_s & ss or used_t & st:
            raise AssertionError('invalid explicit local agreement pieces')
        used_s.update(ss)
        used_t.update(st)
        for v in ss:
            if v not in vertices:
                raise AssertionError('local witness leaves its actual source component')
            owner[v] = index
    while len(owner) < len(vertices):
        frontier = [(v,w) for v in sorted(owner) for w in adjacent[v]
                    if w in vertices and w not in owner]
        if not frontier:
            raise AssertionError('connected source component has no expansion frontier')
        v,w = min(frontier)
        owner[w] = owner[v]
    local_cuts = [e for e,(u,v) in enumerate(S.edges)
                  if u in vertices and v in vertices and owner[u] != owner[v]]
    if len(local_cuts) != max(0,len(blocks)-1):
        raise AssertionError('local original-edge witness accounting failed')
    return {'pieces': [list(b) for b in blocks], 'cost': len(local_cuts),
            'original_local_edge_indices': local_cuts,
            'target_supports': [sorted(T.support(b)) for b in blocks]}


def guard(S, T, budget, cuts):
    if cuts.bit_count() > budget:
        return None
    made = components(S,cuts)
    if made is None:
        return None
    parts, adjacent = made
    r = cuts.bit_count()
    if S.labels and len(parts) != r+1:
        raise AssertionError('original precuts are not nonredundant')
    spans = [T.support(labels) for labels,_ in parts]
    tadj = {v:set() for v in T.parent}
    for u,v in T.edges:
        tadj[u].add(v)
        tadj[v].add(u)
    pure = all(all(len(tadj[v] & spans[i]) == len(tadj[v] & spans[j]) == 2
                   for v in spans[i] & spans[j])
               for i in range(len(parts)) for j in range(i))
    compatible_triple = all(S.restrict(labels) == T.restrict(labels) or len(labels) == 3
                            for labels,_ in parts)
    if not (pure or compatible_triple):
        return None
    witnesses = [witness(S,T,labels,vertices,adjacent) for labels,vertices in parts]
    if any(w['cost'] > budget//2 for w in witnesses):
        return None
    return {'original_source_edge_indices': list(core.bits(cuts)), 'precut_cost': r,
            'terminal_class': 'compatible-triple' if compatible_triple else 'pure-bridge',
            'pure': pure, 'compatible_triple': compatible_triple,
            'original_unmarked_tau_upper_bound': max((w['cost'] for w in witnesses), default=0),
            'components': [{'original_labels':list(labels),'full_original_vertices':sorted(vertices),
                            'source_restriction':core.json_tree(S.restrict(labels)),
                            'target_support':sorted(T.support(labels)), 'local_witness':w}
                           for (labels,vertices),w in zip(parts,witnesses)]}


def verify_certificate(source,target,budget,certificate):
    try:
        S,T = core.validate_input(source,target,budget)
        edges = certificate['original_source_edge_indices']
        if len(set(edges)) != len(edges) or any(not isinstance(e,int) or isinstance(e,bool)
                or e < 0 or e >= len(S.edges) for e in edges):
            return False
        expected = guard(S,T,budget,sum(1 << e for e in edges))
        return expected is not None and certificate == expected
    except (ValueError,KeyError,TypeError):
        return False


def generate(source,target,budget):
    S,T = core.validate_input(source,target,budget)
    original = core.minimal_rows(core.conflicts(S,T))
    outputs, visited = [], set()
    stats = {'states':0,'guard_tests':0,'row_candidates_compiled':0,'empty_component_prunes':0}
    def visit(rows,cuts):
        left = budget-cuts.bit_count()
        if left < 0:
            return
        key = (tuple(rows),cuts,left)
        if key in visited:
            return
        visited.add(key)
        stats['states'] += 1
        if components(S,cuts) is None:
            stats['empty_component_prunes'] += 1
            return
        stats['guard_tests'] += 1
        cert = guard(S,T,budget,cuts)
        if cert is not None:
            if not verify_certificate(source,target,budget,cert):
                raise AssertionError('guarded certificate replay failed')
            outputs.append(cert)
            return
        rows,forced,_ = dag.forced_closure(rows)
        if forced:
            visit(rows,cuts | forced)
            return
        if not rows:
            raise AssertionError('full transversal was not recognized by explicit guard')
        chosen,all_rows = selector.choose_row(rows)
        stats['row_candidates_compiled'] += len(all_rows)
        for child in chosen['kept']:
            if child['delta'] <= left:
                visit(child['rows'],cuts | child['cut_mask'])
    visit(original,0)
    return {'certificates':outputs,'stats':stats,
            'runtime_status':'paid finite search; global alpha bound OPEN'}
