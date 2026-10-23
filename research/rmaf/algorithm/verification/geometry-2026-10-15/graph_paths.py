#!/usr/bin/env python3
"""One-shot pre-candidate geometry instrument; no candidate/prover imports.

Same reviewer lineage as the previous frozen reviews, with no extra independent
replication count. New code uses BFS graph paths, an independent address formula,
and bottom-up rooted restrictions. Literal controls predate this implementation.
This finite checker cannot prove universal graph geometry or a complete solver.
"""
import argparse
import copy
import hashlib
import itertools
import json
import time
from collections import deque
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]

def key(blocks):
    return sorted([sorted(b) for b in blocks], key=lambda b: (len(b), b))

class Original:
    def __init__(self, tree):
        self.raw = tree
        self.children, self.adj, self.labels, self.edges = {}, {}, {}, []
        todo = deque([] if tree is None else [('', tree)])
        while todo:
            address, item = todo.popleft()
            self.adj.setdefault(address, set())
            if isinstance(item, str):
                if item in self.labels:
                    raise ValueError('duplicate label')
                self.labels[item] = address
                self.children[address] = []
            elif isinstance(item, (list, tuple)) and len(item) == 2:
                children = [address+'0', address+'1']
                self.children[address] = children
                for child, subtree in zip(children, item):
                    self.adj.setdefault(child, set()).add(address)
                    self.adj[address].add(child)
                    self.edges.append((address, child))
                    todo.append((child, subtree))
            else:
                raise ValueError('binary node required')

    def path(self, start, finish):
        if start not in self.adj or finish not in self.adj:
            raise ValueError('unknown vertex')
        todo, previous = deque([start]), {start: None}
        while todo and finish not in previous:
            current = todo.popleft()
            for other in sorted(self.adj[current]):
                if other not in previous:
                    previous[other] = current
                    todo.append(other)
        result = {finish}
        while finish != start:
            finish = previous[finish]
            result.add(finish)
        return result

    def hull(self, block):
        block = set(block)
        if not block <= set(self.labels):
            raise ValueError('unknown label')
        addresses = [self.labels[x] for x in sorted(block)]
        vertices = set(addresses)
        for a, b in itertools.combinations(addresses, 2):
            vertices.update(self.path(a, b))
        return vertices

    def address_hull(self, block):
        block = set(block)
        if not block <= set(self.labels):
            raise ValueError('unknown label')
        if not block:
            return set()
        addresses = [self.labels[x] for x in sorted(block)]
        shared = addresses[0]
        for address in addresses[1:]:
            while not address.startswith(shared):
                shared = shared[:-1]
        return {a[:length] for a in addresses
                for length in range(len(shared), len(a)+1)}

    def components(self, vertices, deleted_edges=()):
        vertices = set(vertices)
        deleted = {frozenset(e) for e in deleted_edges}
        unseen, result = set(vertices), []
        while unseen:
            start = min(unseen)
            todo, component = deque([start]), {start}
            unseen.remove(start)
            while todo:
                current = todo.popleft()
                for other in sorted(self.adj[current] & unseen):
                    if frozenset((current, other)) not in deleted:
                        component.add(other)
                        unseen.remove(other)
                        todo.append(other)
            result.append(component)
        return sorted(result, key=lambda c: sorted(c))

    def connected(self, vertices):
        return bool(vertices) and len(self.components(vertices)) == 1

    def convex(self, vertices):
        return all(self.path(a, b) <= set(vertices)
                   for a, b in itertools.combinations(vertices, 2))

    def restriction(self, block):
        block = set(block)
        if not block <= set(self.labels):
            raise ValueError('unknown label')
        selected = {address: label for label, address in self.labels.items()
                    if label in block}
        shapes = {}
        for address in sorted(self.children, key=lambda a: (-len(a), a)):
            if not self.children[address]:
                shapes[address] = ('L', selected[address]) if address in selected else None
            else:
                below = [shapes[x] for x in self.children[address] if shapes[x] is not None]
                shapes[address] = (None if not below else below[0] if len(below) == 1
                                   else ('N', *sorted(below)))
        return shapes.get('')

def nonempty_subsets(block):
    block = sorted(set(block))
    return [list(x) for size in range(1, len(block)+1)
            for x in itertools.combinations(block, size)]

def region_observations(graph, parent, removed, piece=None):
    parent, removed = set(parent), set(removed)
    hull = graph.hull(parent)
    components = graph.components(hull-removed)
    component_labels = [{label for label in parent if graph.labels[label] in component}
                        for component in components]
    regions = [labels for labels in component_labels if labels]
    leafless = [sorted(component) for component, labels in zip(components, component_labels)
                if not labels]
    avoiding, mismatches, occupancy = [], [], []
    ordered_removed = sorted(removed)
    for block in nonempty_subsets(parent):
        ph = graph.hull(block)
        avoids = not bool(ph & removed)
        monochromatic = any(set(block) <= region for region in regions)
        if avoids:
            avoiding.append(block)
        if avoids != monochromatic:
            mismatches.append({'piece': block, 'avoids': avoids,
                               'one_region': monochromatic})
        occupancy.append([v in ph for v in ordered_removed])
    guard = bool(removed) and all(v in hull and v not in graph.labels.values()
                                  and len(graph.adj[v] & hull) >= 2 for v in removed)
    result = dict(leaf_regions=key(regions), leafless_components=sorted(leafless),
                  r=len(regions), overlap_guard=guard,
                  covers_parent_labels=set().union(*regions) == parent if regions else not parent,
                  avoiding_subsets=key(avoiding), equivalence=not mismatches,
                  equivalence_failures=mismatches,
                  coincidence=(all(row[0] == row[1] for row in occupancy)
                               if len(removed) == 2 else None),
                  full_components=[{'vertices': sorted(c), 'parent_labels': sorted(l)}
                                   for c, l in zip(components, component_labels)])
    if piece is not None:
        ph = graph.hull(piece)
        result['piece_occupancy'] = [v in ph for v in ordered_removed]
    return result

def helly_observations(graph, vertex_sets):
    vertex_sets = [set(x) for x in vertex_sets]
    if len(vertex_sets) != 3 or any(not x <= set(graph.adj) for x in vertex_sets):
        raise ValueError('three known vertex sets required')
    connected = [graph.connected(x) for x in vertex_sets]
    pairwise = [bool(vertex_sets[i] & vertex_sets[j]) for i,j in [(0,1),(0,2),(1,2)]]
    common = set.intersection(*vertex_sets)
    common_edges = [list(e) for e in graph.edges
                    if all(set(e) <= vertices for vertices in vertex_sets)]
    return dict(pairwise=pairwise, connected=connected,
                common_vertices=sorted(common), common_edges=sorted(common_edges),
                common_vertex_exists=bool(common), common_edge_exists=bool(common_edges),
                premise=all(connected) and all(pairwise),
                selector=min(common) if common else None)

def state_observations(target, source_trees, partition, vertices):
    target = Original(target)
    sources = [Original(s) for s in source_trees]
    source_labels = [label for source in sources for label in source.labels]
    flat = [label for block in partition for label in block]
    result = dict(valid=False)
    if len(source_labels) != len(set(source_labels)) or set(source_labels) != set(target.labels):
        return dict(result, reason='source labels do not partition target labels')
    if any(not b for b in partition) or len(flat) != len(set(flat)) or set(flat) != set(target.labels):
        return dict(result, reason='final blocks do not partition original labels')
    owners = [[i for i, source in enumerate(sources) if set(block) <= set(source.labels)]
              for block in partition]
    if any(len(x) != 1 for x in owners):
        return dict(result, reason='piece has no unique source parent')
    owners = [x[0] for x in owners]
    hulls = [target.hull(block) for block in partition]
    all_owners = {v: sorted({owner for owner, h in zip(owners, hulls) if v in h})
                  for v in target.adj}
    result.update(vertex_owners=[all_owners.get(v, []) for v in vertices],
                  max_parent_owners=max([len(x) for x in all_owners.values()], default=0))
    for block, owner in zip(partition, owners):
        if target.restriction(block) != sources[owner].restriction(block):
            return dict(result, reason='rooted restriction mismatch')
    if any(hulls[i] & hulls[j] for i,j in itertools.combinations(range(len(hulls)), 2)):
        return dict(result, reason='target hull overlap')
    for i, source in enumerate(sources):
        hs = [source.hull(block) for block, owner in zip(partition, owners) if owner == i]
        if any(a & b for a,b in itertools.combinations(hs, 2)):
            return dict(result, reason='source hull overlap')
    result.update(valid=True, components=len(partition),
                  additional_cuts=len(partition)-len(sources))
    return result

def cut_observations(graph, cuts):
    cuts = [tuple(e) for e in cuts]
    if len(set(cuts)) != len(cuts):
        raise ValueError('duplicate cut')
    if any(edge not in graph.edges for edge in cuts):
        raise ValueError('nonexistent edge')
    components = graph.components(graph.adj, cuts)
    blocks = [{label for label,address in graph.labels.items() if address in c}
              for c in components]
    return dict(partition=key(b for b in blocks if b),
                empty_components=sorted(sorted(c) for c,b in zip(components, blocks) if not b),
                graph_components=len(components), paid=len(cuts),
                nonredundant=all(blocks) and len(components) == len(cuts)+1)

def observe(case):
    kind = case['kind']
    if kind == 'state':
        return state_observations(case['target'], case['sources'], case['partition'], case['vertices'])
    if kind == 'forest_cuts':
        rows = [cut_observations(Original(s), cuts)
                for s,cuts in zip(case['sources'], case['per_source_cuts'])]
        parts = key(block for row in rows for block in row['partition'])
        state = state_observations(case['target'], case['sources'], parts, [])
        return dict(paid=sum(row['paid'] for row in rows), components=len(parts),
                    partition=parts, valid=state['valid'], source_cuts=rows,
                    source_qualified_edges=[[i,*edge] for i,cuts in enumerate(case['per_source_cuts'])
                                            for edge in cuts])
    graph = Original(case['tree'])
    if kind == 'hull':
        hull, address = graph.hull(case['block']), graph.address_hull(case['block'])
        return dict(hull=sorted(hull), address_hull=sorted(address),
                    connected=graph.connected(hull), convex=graph.convex(hull),
                    root_exists='' in graph.adj, root_in_hull='' in hull,
                    leaf_addresses=graph.labels)
    if kind == 'helly':
        return helly_observations(graph, [graph.hull(b) for b in case['blocks']])
    if kind == 'sets_helly':
        return helly_observations(graph, case['vertex_sets'])
    if kind == 'regions':
        return region_observations(graph, case['parent'], case['removed'], case.get('piece'))
    if kind == 'chain':
        hulls = [graph.hull(block) for block in case['parents']]
        v,w = case['v'],case['w']
        middle = region_observations(graph, case['parents'][1], [v,w], case.get('piece'))
        result = dict(overlap_edges=[[i,j] for i,j in itertools.combinations(range(3),2) if hulls[i]&hulls[j]],
                      endpoints_disjoint=not bool(hulls[0]&hulls[2]),
                      chosen_overlap_vertices=v in hulls[0]&hulls[1] and w in hulls[1]&hulls[2] and v != w,
                      middle_r=middle['r'], middle_leafless_components=middle['leafless_components'],
                      middle_coincidence=middle['coincidence'], middle=middle,
                      original_hulls=[sorted(h) for h in hulls])
        if 'piece_occupancy' in middle:
            result['piece_occupancy'] = middle['piece_occupancy']
        return result
    if kind == 'cuts':
        return cut_observations(graph, case['cuts'])
    if kind == 'error':
        if case['operation'] == 'hull':
            graph.hull(case['block'])
        elif case['operation'] == 'cuts':
            cut_observations(graph, case['cuts'])
        return {'unexpectedly_accepted': True}
    raise ValueError('unknown control kind')

def compare(observed, expected):
    failures = []
    for name, value in expected.items():
        if observed.get(name) != value:
            actual = observed.get(name)
            residual = (actual-value if type(actual) is int and type(value) is int else None)
            failures.append(dict(field=name, expected=value, observed=actual, residual=residual))
    return failures

def run(pin, phase):
    cases = pin['cases']
    ids = pin['plant_first_ids']
    cases = ([next(c for c in cases if c['id'] == id) for id in ids] if phase == 'pilot'
             else sorted(cases, key=lambda c: (c['id'] not in ids, cases.index(c))))
    rows = []
    started = time.perf_counter()
    for case in cases:
        before = time.perf_counter()
        if case['kind'] == 'error':
            try:
                observe(case)
            except ValueError as error:
                observed = {'error': str(error)}
            else:
                observed = {'error': None}
            failures = compare(observed, {'error': case['expected_error']})
        else:
            observed = observe(case)
            failures = compare(observed, case['expected'])
        plants = []
        if not failures:
            for plant in case.get('plants', []):
                bad = compare(observed, plant['override'])
                plants.append(dict(id=plant['id'], caught=bool(bad), exact_failures=bad))
                if not bad:
                    failures.append({'plant_survived': plant['id']})
        row = dict(id=case['id'], kind=case['kind'], observed=observed,
                   clean_passed=not failures, failures=failures, plants=plants,
                   elapsed_seconds=time.perf_counter()-before)
        rows.append(row)
        print(json.dumps({'completed':len(rows),'id':case['id'],'passed':not failures}),flush=True)
        if failures:
            break
    return dict(phase=phase, declared_controls=len(cases), completed=len(rows),
                passed=sum(row['clean_passed'] for row in rows),
                plants_caught=sum(plant['caught'] for row in rows for plant in row['plants']),
                plant_count=sum(len(row['plants']) for row in rows), rows=rows,
                elapsed_seconds=time.perf_counter()-started,
                all_passed=len(rows)==len(cases) and all(row['clean_passed'] for row in rows))

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--phase', choices=['pilot','controls'], required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    pin_path = HERE/'CONTROL-PIN.json'
    freeze = json.loads((HERE/'PRE-CANDIDATE-FREEZE.json').read_text())
    for path, expected in freeze['files_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected, path
    result = run(json.loads(pin_path.read_text()), args.phase)
    receipt = dict(scope='pre-candidate finite instrument controls; no universal scientific claim',
                   same_reviewer_lineage=True, additional_independent_replications=0,
                   candidate_source_read=False, source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   controls_sha256=hashlib.sha256(pin_path.read_bytes()).hexdigest(), result=result)
    assert not args.out.exists()
    args.out.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['phase','declared_controls','completed','passed','plant_count','plants_caught','elapsed_seconds','all_passed']}))
    if not result['all_passed']:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
