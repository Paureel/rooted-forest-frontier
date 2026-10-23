#!/usr/bin/env python3
"""One-shot finite integration-review instrument; no toolkit registration.

Build explicit integer-vertex original graphs. Compute hulls by terminal
pruning, restrictions by bottom-up graph signatures, cuts by components, and
current states by flat records. No candidate, prover, or old verifier imports.
Run frozen literal controls only; output exact comparisons and caught false
expectations. A passing finite battery is instrument readiness, not coverage.
"""
import argparse
from collections import Counter, deque
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from time import perf_counter

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

class Graph:
    def __init__(self, tree):
        self.address = {}
        self.at = {}
        self.child = {}
        self.label = {}
        self.adj = {}
        queue = deque([(tree, '', None)])
        while queue:
            item, address, parent = queue.popleft()
            i = len(self.address)
            self.address[i] = address
            self.at[address] = i
            self.child[i] = []
            self.adj[i] = set()
            if parent is not None:
                self.child[parent].append(i)
                self.adj[parent].add(i)
                self.adj[i].add(parent)
            if isinstance(item, int):
                self.label[i] = item
            else:
                assert len(item) == 2
                queue.extend([(item[0], address + '0', i), (item[1], address + '1', i)])
        self.labels = self.ordered_labels()

    def ordered_labels(self):
        result, pending = [], [0]
        while pending:
            i = pending.pop()
            if i in self.label:
                result.append(self.label[i])
            else:
                pending.extend(reversed(self.child[i]))
        return result

    def hull(self, selected):
        terminals = {i for i, x in self.label.items() if x in selected}
        if not terminals:
            return set()
        alive = set(self.address)
        neighbors = {i: set(v) for i, v in self.adj.items()}
        todo = deque(i for i in alive if len(neighbors[i]) <= 1 and i not in terminals)
        while todo:
            i = todo.popleft()
            if i not in alive:
                continue
            alive.remove(i)
            for j in tuple(neighbors[i]):
                neighbors[j].discard(i)
                if j in alive and len(neighbors[j]) <= 1 and j not in terminals:
                    todo.append(j)
            neighbors[i].clear()
        return alive

    def signature(self, selected):
        image = {}
        for i in reversed(list(self.address)):
            if i in self.label:
                image[i] = ('L', self.label[i]) if self.label[i] in selected else None
            else:
                children = [image[j] for j in self.child[i] if image[j] is not None]
                image[i] = (None if not children else children[0] if len(children) == 1
                            else ('N', tuple(sorted(children, key=repr))))
        return image[0]

    def embeddings(self, blocks):
        spans = [self.hull(b) for b in blocks]
        return all(not (a & b) for i, a in enumerate(spans) for b in spans[i + 1:])

    def actual_edge(self, u, v):
        return u in self.at and v in self.at and self.at[v] in self.adj[self.at[u]]

    def connected_addresses(self, support):
        if any(v not in self.at for v in support):
            return False
        if not support:
            return True
        nodes = {self.at[v] for v in support}
        seen, pending = set(), [next(iter(nodes))]
        while pending:
            i = pending.pop()
            if i in seen:
                continue
            seen.add(i)
            pending.extend((self.adj[i] & nodes) - seen)
        return seen == nodes

def partition(labels, blocks):
    flat = [x for b in blocks for x in b]
    count = Counter(flat)
    return all(blocks) and all(count[x] == 1 for x in labels) and all(x in labels for x in flat)

def canonical(blocks):
    return sorted(sorted(b) for b in blocks)

class Current:
    def __init__(self, graph, colors, custom=None):
        self.records = {}
        if custom is None:
            for i in reversed(list(graph.address)):
                self.records[i] = ({'origin': graph.address[i], 'labels': [graph.label[i]],
                                    'color': colors[graph.label[i]]} if i in graph.label
                                   else {'origin': graph.address[i], 'kids': graph.child[i][:]})
            self.root = 0
        else:
            self.root = 0
            todo = deque([(0, custom)])
            serial = 1
            while todo:
                i, item = todo.popleft()
                if item[0] == 'g':
                    self.records[i] = {'origin': item[1], 'labels': item[2][:], 'color': item[3]}
                else:
                    a, b = serial, serial + 1
                    serial += 2
                    self.records[i] = {'origin': item[1], 'kids': [a, b]}
                    todo.extend([(a, item[2]), (b, item[3])])

    def order(self):
        if self.root is None:
            return []
        result, todo = [], [self.root]
        while todo:
            i = todo.pop()
            result.append(i)
            todo.extend(reversed(self.records[i].get('kids', [])))
        return result

    def groups(self):
        return [[self.records[i]['origin'], self.records[i]['labels'][:], self.records[i]['color']]
                for i in self.order() if 'labels' in self.records[i]]

    def root_origin(self):
        return None if self.root is None else self.records[self.root]['origin']

    def normalize(self):
        for i in reversed(self.order()):
            r = self.records[i]
            kids = r.get('kids')
            if kids:
                a, b = (self.records[j] for j in kids)
                if 'labels' in a and 'labels' in b and a['color'] == b['color']:
                    self.records[i] = {'origin': r['origin'], 'labels': a['labels'] + b['labels'],
                                       'color': a['color']}
        return self

    def erase(self, origin):
        image = {}
        for i in reversed(self.order()):
            r = self.records[i]
            if r['origin'] == origin:
                image[i] = None
            elif 'labels' in r:
                image[i] = i
            else:
                children = [image[j] for j in r['kids'] if image[j] is not None]
                if len(children) == 2:
                    self.records[i]['kids'] = children
                    image[i] = i
                else:
                    image[i] = children[0] if children else None
        self.root = image[self.root] if self.root is not None else None
        return self

    def identity(self):
        return [(i, deepcopy(self.records[i])) for i in self.order()]

def state(data):
    g = Graph(data['tree'])
    c = Current(g, data['colors'], data.get('current'))
    if data.get('normalize', True):
        c.normalize()
    return g, c

def owner_ids(groups, blocks):
    ids = []
    for _, labels, _ in groups:
        owners = {i for i, b in enumerate(blocks) for x in labels if x in b}
        ids.append(next(iter(owners)) if len(owners) == 1 and
                   all(any(x in b for b in blocks) for x in labels) else None)
    return ids

def evaluate(op, d):
    if op == 'partition':
        return {'partition': bool(partition(d['labels'], d['blocks']))}
    if op == 'embedding':
        return {'embeddings': Graph(d['tree']).embeddings(d['blocks'])}
    if op == 'agreement':
        a, b = Graph(d['left']), Graph(d['right'])
        blocks = d['blocks']
        proper = len(set(a.labels)) == len(a.labels) and len(set(b.labels)) == len(b.labels) and sorted(a.labels) == sorted(b.labels)
        agrees = partition(a.labels, blocks) and partition(b.labels, blocks)
        agrees = agrees and all(a.signature(q) is not None and a.signature(q) == b.signature(q) for q in blocks)
        agrees = agrees and a.embeddings(blocks) and b.embeddings(blocks)
        return {'proper_inputs': proper, 'agreement': bool(agrees)}
    if op in {'normalize', 'owners', 'erase', 'surviving_owner', 'choose', 'attempt'}:
        graph, current = state(d)
        if op == 'normalize':
            before = current.identity()
            groups, root = current.groups(), current.root_origin()
            return {'root_origin': root, 'groups': groups,
                    'idempotent': before == current.normalize().identity()}
        if op == 'owners':
            groups = current.groups()
            owners = owner_ids(groups, d['blocks'])
            mono = all(len({d['colors'][x] for x in labels}) == 1 for _, labels, _ in groups)
            return {'monochromatic_groups': mono, 'each_group_has_one_owner': None not in owners,
                    'group_owner_ids': owners}
        if op in {'erase', 'surviving_owner'}:
            current.erase(d['chosen'])
            if op == 'erase':
                return {'root_origin': current.root_origin(), 'groups': current.groups()}
            owners = owner_ids(current.groups(), d['blocks'])
            assert len(owners) == 1
            return {'root_origin': current.root_origin(), 'surviving_owner': owners[0],
                    'original_root_survives': any(current.records[i]['origin'] == '' for i in current.order())}
        if op == 'choose':
            groups = current.groups()
            counts = Counter(g[2] for g in groups)
            if len(counts) == 1:
                return {'kind': 'finish', 'origins': []}
            unique = [g for g in groups if counts[g[2]] == 1]
            if unique:
                return {'kind': 'one', 'origins': [unique[0][0]]}
            for i in current.order():
                kids = current.records[i].get('kids')
                if kids and all('labels' in current.records[j] for j in kids):
                    a, b = (current.records[j] for j in kids)
                    return ({'kind': 'refuse-unnormalized', 'origins': []} if a['color'] == b['color']
                            else {'kind': 'two', 'origins': [a['origin'], b['origin']]})
            return {'kind': 'refuse-no-cherry', 'origins': []}
        chosen = d['group']
        origins = [current.records[i]['origin'] for i in current.order()]
        member = chosen in current.groups()
        outcome = 'root' if chosen[0] == '' else 'duplicate' if chosen[0] in d['cuts'] else None
        edge = chosen[0] != '' and chosen[0] in graph.at
        if outcome is None:
            current.erase(chosen[0])
            outcome = 'entire' if current.root is None else 'continued'
        continued = outcome == 'continued'
        return {'guard_outcome': outcome, 'child_attempts': 1, 'continuation_called': continued,
                'chosen_is_current_group': member, 'current_origins_unique': len(set(origins)) == len(origins),
                'chosen_origin_is_actual_edge': edge,
                'next_root': current.root_origin() if continued else None,
                'next_groups': current.groups() if continued else []}
    if op == 'refinement':
        def refines(a, b):
            return all(any(set(x) <= set(y) for y in b) for x in a)
        return {'F_refines_Q': refines(d['F'], d['Q']), 'Q_refines_F': refines(d['Q'], d['F'])}
    if op == 'source_partition':
        graph = Graph(d['tree'])
        blocks = d['blocks']
        supports = ([{graph.address[v] for v in graph.hull(b)} for b in blocks]
                    if d['supports'] == 'minimal' else [set(s) for s in d['supports']])
        owner = {x: i for i, b in enumerate(blocks) for x in b}
        actual = all(v in graph.at for s in supports for v in s)
        terminal_exact = partition(graph.labels, blocks) and all(
            (graph.address[v] in s) == (owner[x] == i)
            for i, s in enumerate(supports) for v, x in graph.label.items())
        connected = all(graph.connected_addresses(s) for s in supports)
        disjoint = all(not (s & t) for i, s in enumerate(supports) for t in supports[i + 1:])
        leaf_addresses = {graph.address[v] for v in graph.label}
        leafless = any(bool(s) and not (s & leaf_addresses) for s in supports)
        return {'actual': actual, 'terminal_exact': bool(terminal_exact), 'connected': connected,
                'disjoint': disjoint, 'valid': bool(actual and terminal_exact and connected and disjoint),
                'leafless_support': leafless,
                'monochromatic': all(len({d['colors'][x] for x in b}) <= 1 for b in blocks),
                'chosen_singletons': [len(blocks[owner[x]]) == 1 for x in d['chosen']]}
    if op == 'edges':
        graph = Graph(d['tree'])
        return {'actual': [graph.actual_edge(u, v) for u, v in d['pairs']]}
    if op == 'cuts':
        graph = Graph(d['tree'])
        cuts = d['cuts']
        actual = all(v != '' and v in graph.at for v in cuts)
        forbidden = {frozenset((graph.at[v[:-1]], graph.at[v])) for v in cuts if v and v in graph.at}
        unseen = set(graph.address)
        components = []
        while unseen:
            todo = [next(iter(unseen))]
            component = set()
            while todo:
                i = todo.pop()
                if i not in unseen:
                    continue
                unseen.remove(i)
                component.add(i)
                todo.extend(j for j in graph.adj[i] if frozenset((i, j)) not in forbidden)
            components.append(component)
        regions = [sorted(graph.label[v] for v in c if v in graph.label) for c in components]
        leafless = sum(not b for b in regions)
        regions = canonical([b for b in regions if b])
        distinct = len(set(cuts)) == len(cuts)
        exact = (actual and distinct and leafless == 0 and regions == canonical(d['partition'])
                 and len(cuts) + 1 == len(d['partition']))
        return {'actual_edges': actual, 'distinct': distinct, 'components': len(components),
                'leafless_components': leafless, 'leaf_regions': regions, 'cut_count': len(cuts),
                'exact_partition_and_cost': exact}
    raise ValueError(op)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--phase', required=True, choices=['pilot', 'size-pilot', 'controls'])
    parser.add_argument('--receipt', required=True)
    args = parser.parse_args()
    pinned = json.loads((HERE / 'CONTROL-PIN.json').read_text())
    controls = pinned['controls']
    assert len(controls) == pinned['count'] > 0
    if args.phase == 'pilot':
        controls = controls[:3]
    elif args.phase == 'size-pilot':
        controls = controls[7:13]
    started = perf_counter()
    rows = []
    for item in controls:
        tick = perf_counter()
        actual = evaluate(item['op'], item['input'])
        false = deepcopy(item['expected'])
        false[item['false_expectation']['field']] = item['false_expectation']['value']
        assert false != item['expected'], item['id']
        row = {'id': item['id'], 'actual': actual, 'expected': item['expected'],
               'clean_passed': actual == item['expected'], 'false_expectation': false,
               'false_expectation_caught': actual != false,
               'elapsed_seconds': perf_counter() - tick}
        rows.append(row)
        if not row['clean_passed'] or not row['false_expectation_caught']:
            print(json.dumps({'FAILED': row}))
            break
    all_passed = len(rows) == len(controls) and all(r['clean_passed'] and r['false_expectation_caught'] for r in rows)
    receipt = {'created_utc': datetime.now(timezone.utc).isoformat(), 'phase': args.phase,
               'scope': 'instrument readiness only; no integration candidate content inspected',
               'source_sha256': sha(Path(__file__)), 'control_sha256': sha(HERE / 'CONTROL-PIN.json'),
               'freeze_sha256': sha(HERE / 'PRE-CANDIDATE-FREEZE.json'),
               'declared_controls': len(controls), 'completed': len(rows),
               'clean_passed': sum(r['clean_passed'] for r in rows),
               'false_expectations': len(controls),
               'false_expectations_caught': sum(r['false_expectation_caught'] for r in rows),
               'all_passed': all_passed, 'elapsed_seconds': perf_counter() - started, 'rows': rows}
    dest = ROOT / args.receipt
    assert not dest.exists()
    dest.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'rows'}))
    raise SystemExit(0 if all_passed else 1)

if __name__ == '__main__':
    main()
