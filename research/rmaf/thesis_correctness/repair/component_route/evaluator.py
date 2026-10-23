#!/usr/bin/env python3
"""One-shot independent component/partition evaluator for normalization repair.

No project evaluator is imported. A forest is recognized by matching rooted
induced subtrees on its leaf blocks and checking disjoint minimal embeddings.
Shared inputs are primary definitions and the frozen controls, not other code.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
from itertools import combinations
import json
from pathlib import Path
import time

BASE = Path('/Users/paurel/Documents/ChatGPT/bootscience')
ROUTE = BASE / 'research/rmaf/thesis_correctness/repair/component_route'
RESULTS = BASE / 'research/rmaf/results'
PROGRESS = BASE / 'research/rmaf/progress/thesis-correctness-repair-component.json'


def atomic(path, value):
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    tmp.replace(path)


@dataclass
class Forest:
    children: dict[int, tuple[int, ...]]
    label: dict[int, str]

    def __post_init__(self):
        self.parent = {c: v for v, cs in self.children.items() for c in cs}
        self.roots = tuple(v for v in self.children if v not in self.parent)
        self.by_label = {s: v for v, s in self.label.items()}
        assert len(self.by_label) == len(self.label)
        assert all(v in self.children for v in self.label)
        assert len(self.parent) == sum(map(len, self.children.values()))
        self._desc = {}
        self._sig = {}
        visited = set()
        def visit(v):
            assert v not in visited
            visited.add(v)
            for c in self.children[v]:
                visit(c)
            self._desc[v] = frozenset(([self.label[v]] if v in self.label else []) +
                                     [s for c in self.children[v] for s in self._desc[c]])
            cs = tuple(sorted((self._sig[c] for c in self.children[v]), key=repr))
            self._sig[v] = (self.label.get(v), cs)
        for r in self.roots:
            visit(r)
        assert visited == set(self.children)

    @classmethod
    def tree(cls, nested):
        children = {0: ()}
        labels = {0: 'rho'}
        def add(t):
            v = len(children)
            children[v] = ()
            if isinstance(t, str):
                labels[v] = t
            else:
                assert len(t) == 2
                children[v] = tuple(add(c) for c in t)
            return v
        children[0] = (add(nested),)
        return cls(children, labels)

    @property
    def edges(self):
        # Each current edge is identified by its original bottom endpoint.
        return frozenset(self.parent)

    def desc(self, v):
        return self._desc[v]

    def signature(self, v):
        return self._sig[v]

    def blocks(self):
        return frozenset(self.desc(r) for r in self.roots)

    def node(self, cluster):
        s = frozenset([cluster] if isinstance(cluster, str) else cluster)
        matches = [v for v in self.children if self.desc(v) == s]
        assert len(matches) == 1, ('ambiguous/missing cluster', sorted(s), matches)
        return matches[0]

    def edge_ids(self, clusters):
        ans = frozenset(self.node(s) for s in clusters)
        assert ans <= self.edges
        return ans

    def edge_clusters(self, edges):
        return sorted((sorted(self.desc(v)) for v in edges), key=lambda a: (len(a), a))

    def chain(self, v):
        ans = [v]
        while v in self.parent:
            v = self.parent[v]
            ans.append(v)
        return ans

    def path(self, a, c):
        aa, cc = self.chain(a), self.chain(c)
        shared = set(cc)
        u = next((v for v in aa if v in shared), None)
        if u is None:
            return None
        av, cv = aa[:aa.index(u)], cc[:cc.index(u)]
        return u, frozenset(av + cv), frozenset(av + [u] + cv)

    def yielded(self, cuts):
        assert set(cuts) <= self.edges
        cc, ll = {}, {}
        def reduce(v):
            cs = [w for c in self.children[v] if c not in cuts
                  if (w := reduce(c)) is not None]
            if v not in self.label and len(cs) < 2:
                return cs[0] if cs else None
            cc[v] = tuple(cs)
            if v in self.label:
                ll[v] = self.label[v]
            return v
        for r in tuple(self.roots) + tuple(cuts):
            reduce(r)
        return Forest(cc, ll)

    def embedding(self, block):
        vs = [self.by_label[s] for s in sorted(block)]
        keep = {vs[0]}
        for v in vs[1:]:
            p = self.path(vs[0], v)
            if p is None:
                return None
            keep.update(p[2])
        return frozenset(keep)

    def restricted(self, block):
        keep = self.embedding(block)
        if keep is None:
            return None
        root = next(v for v in keep if self.parent.get(v) not in keep)
        cc, ll = {}, {}
        def reduce(v):
            cs = [reduce(c) for c in self.children[v] if c in keep]
            if v not in self.label and len(cs) == 1:
                return cs[0]
            assert v in self.label or len(cs) >= 2
            cc[v] = tuple(cs)
            if v in self.label:
                ll[v] = self.label[v]
            return v
        rr = reduce(root)
        f = Forest(cc, ll)
        return f, rr, keep

    def from_blocks(self, blocks):
        cc, ll, used = {}, {}, set()
        for b in blocks:
            got = self.restricted(b)
            assert got is not None
            f, _, keep = got
            assert not (used & keep), 'overlapping partition is not a forest'
            used.update(keep)
            cc.update(f.children)
            ll.update(f.label)
        assert set(ll.values()) == set(self.label.values())
        return Forest(cc, ll)


def is_forest(candidate, source):
    if set(candidate.label.values()) != set(source.label.values()):
        return {'ok': False, 'reason': 'label_set'}
    used = set()
    for r in candidate.roots:
        block = candidate.desc(r)
        got = source.restricted(block)
        if got is None:
            return {'ok': False, 'reason': 'block_spans_components', 'block': sorted(block)}
        f, rr, embedding = got
        if f.signature(rr) != candidate.signature(r):
            return {'ok': False, 'reason': 'rooted_topology', 'block': sorted(block),
                    'candidate': candidate.signature(r), 'source_restriction': f.signature(rr)}
        if used & embedding:
            return {'ok': False, 'reason': 'overlap', 'block': sorted(block),
                    'shared_vertices': sorted(used & embedding)}
        used.update(embedding)
    return {'ok': True}


def af(candidate, *sources):
    legs = [is_forest(candidate, f) for f in sources]
    return {'ok': all(x['ok'] for x in legs), 'legs': legs}


def contained(f2, f1):
    return all(any(b <= a for a in f1.blocks()) for b in f2.blocks())


def sibling_pair(f1, f2, left, right):
    try:
        a, c, aa, cc = f1.node(left), f1.node(right), f2.node(left), f2.node(right)
    except AssertionError:
        return False
    return (a in f1.parent and c in f1.parent and f1.parent[a] == f1.parent[c] and
            aa in f2.parent and cc in f2.parent and f2.parent[aa] == f2.parent[cc] and
            f1.signature(a) == f2.signature(aa) and f1.signature(c) == f2.signature(cc))


def side_edges(f2, a, c):
    _, _, vertices = f2.path(a, c)
    return frozenset(w for v in vertices - {a, c} for w in f2.children[v] if w not in vertices)


def normalized(f2, cuts, a, c):
    u, path_edges, _ = f2.path(a, c)
    removed = cuts & path_edges
    out = set(cuts) - removed
    if len(removed) >= 2 and u in f2.parent:
        out.add(u)
    return frozenset(out), {'path_removed': f2.edge_clusters(removed),
                           'lca_cluster': sorted(f2.desc(u)),
                           'lca_parent_exists': u in f2.parent,
                           'cut_cost_before': len(cuts), 'cut_cost_after': len(out)}


def inspect_case(t1, t2, f1, f2, pair, cuts, e2):
    a, c = (f2.node(s) for s in pair)
    reduced = f2.yielded(cuts)
    nc, info = normalized(f2, cuts, a, c)
    normalized_forest = f2.yielded(nc)
    validity = af(f1, t1)['ok'] and af(f2, t2)['ok']
    initial_agreement = af(reduced, t1, t2)
    compatibility = af(reduced, f1, f2)
    hypotheses = {'finite_binary_forests_of_source_trees': validity,
                  'active_containment': contained(f2, f1),
                  'original_AF': initial_agreement['ok'],
                  'active_AF_compatibility': compatibility['ok'],
                  'E2_subset_E': e2 <= cuts,
                  'common_sibling_after_E2': sibling_pair(f1, f2.yielded(e2), *pair)}
    res = {'hypotheses': hypotheses,
           'in_target_regime': all(hypotheses.values()),
           'original_blocks': sorted(map(sorted, reduced.blocks())),
           'normalized_blocks': sorted(map(sorted, normalized_forest.blocks())),
           'cuts': f2.edge_clusters(cuts), 'E2': f2.edge_clusters(e2),
           'normalized_cuts': f2.edge_clusters(nc),
           'normalized_AF': af(normalized_forest, t1, t2),
           'normalized_active_AF': af(normalized_forest, f1, f2), **info}
    return res


def all_subsets(items):
    items = sorted(items)
    for n in range(len(items) + 1):
        for s in combinations(items, n):
            yield frozenset(s)


def assert_equal(got, want, field):
    if got != want:
        raise AssertionError({'field': field, 'actual': got, 'expected': want})


def replay_controls():
    data = json.loads((ROUTE.parent / 'controls.json').read_text())
    rows = []
    for control in data['controls']:
        t1, t2 = Forest.tree(control['T1']), Forest.tree(control['T2'])
        f1 = t1.from_blocks(control['F1_blocks']) if 'F1_blocks' in control else t1
        f2 = t2.yielded(t2.edge_ids(control.get('F2_initial_cut_clusters', [])))
        pair = control['pair']
        cuts = f2.edge_ids(control['cut_clusters'])
        if control['id'] == 'raw-cover-failure':
            opts = []
            for candidate in all_subsets(f2.edges):
                if opts and len(candidate) > len(opts[0]):
                    break
                if af(f2.yielded(candidate), t1, t2)['ok']:
                    opts.append(candidate)
            a, c = [f2.node(x) for x in pair]
            pendant = side_edges(f2, a, c)
            covered = lambda ss: a in ss or c in ss or pendant <= ss
            row = {'id': control['id'], 'optimum_cuts': len(opts[0]),
                   'optimum_count': len(opts), 'original_AF': af(f2.yielded(cuts), t1, t2)['ok'],
                   'blocks': sorted(map(sorted, f2.yielded(cuts).blocks())),
                   'universal_raw_cover': all(map(covered, opts)),
                   'existential_covered_optimum': any(map(covered, opts))}
            assert_equal(row['optimum_cuts'], control['expected_optimum_cuts'], 'optimum_cuts')
            assert_equal(sorted(map(sorted, control['expected_blocks'])), row['blocks'], 'blocks')
            assert_equal(row['universal_raw_cover'], control['expected_universal_raw_cover'], 'universal_cover')
            assert_equal(row['existential_covered_optimum'], control['expected_existential_covered_optimum'], 'existential_cover')
        else:
            e2 = f2.edge_ids(control.get('E2_clusters', []))
            row = {'id': control['id'], **inspect_case(t1, t2, f1, f2, pair, cuts, e2)}
            for expected, actual in [('expected_original_AF', row['hypotheses']['original_AF']),
                                     ('expected_normalized_AF', row['normalized_AF']['ok']),
                                     ('expected_active_containment', row['hypotheses']['active_containment'])]:
                assert_equal(actual, control[expected], expected)
            if 'expected_lca_parent_exists' in control:
                assert_equal(row['lca_parent_exists'], control['expected_lca_parent_exists'], 'lca_parent_exists')
            assert_equal(row['normalized_cuts'], sorted(control['normalized_cut_clusters'], key=lambda a:(len(a), a)), 'normalized_cuts')
        rows.append(row)
    corruptions = []
    checks = [(rows[0]['optimum_cuts'], 3, 'wrong_optimum'),
              (rows[1]['normalized_AF']['ok'], True, 'bad_normalization_blessed'),
              (rows[1]['hypotheses']['active_containment'], True, 'containment_omitted'),
              (rows[3]['lca_parent_exists'], True, 'fake_parent')]
    for got, want, name in checks:
        caught = False
        try:
            assert_equal(got, want, name)
        except AssertionError:
            caught = True
        assert caught
        corruptions.append({'id': name, 'caught': caught})
    # Null: an untouched tree is precisely its own induced forest.
    null = Forest.tree(['a', 'b'])
    assert af(null.yielded(set()), null)['ok']
    assert len(null.yielded(set()).blocks()) == 1
    return {'controls': rows, 'negative_controls': corruptions, 'null_control': True}


def compound_hunt():
    # Candidate was written before first execution. c has two ordinary labels;
    # E removes both, so no label survives below c at the connecting skeleton.
    c = ['c1', 'c2']
    tree1 = [[['a', c], 'b'], 'd']
    tree2 = [['a', c], ['b', 'd']]
    t1, t2 = Forest.tree(tree1), Forest.tree(tree2)
    cuts = t2.edge_ids([['a'], ['c1'], ['c2']])
    row = inspect_case(t1, t2, t1, t2, ['a', ['c1', 'c2']], cuts, frozenset())
    return {'id': 'compound-sibling-erasure', 'T1': tree1, 'T2': tree2,
            'F1_initial_cuts': [], 'F2_initial_cuts': [],
            'pair': ['a', ['c1', 'c2']], **row}


def all_trees(labels):
    labels = tuple(sorted(labels))
    if len(labels) == 1:
        return [labels[0]]
    first, rest = labels[0], labels[1:]
    out = []
    for count in range(len(rest)):
        for tail in combinations(rest, count):
            left = (first,) + tail
            right = tuple(x for x in rest if x not in tail)
            for a in all_trees(left):
                for b in all_trees(right):
                    out.append([a, b])
    return out


def root_pilot(limit):
    # Every F2 has the rho edge cut, hence LCA=root is a genuine structural
    # boundary, not an unexecuted premise from an algorithm trace.
    trees = all_trees(('a', 'b', 'c', 'd'))
    count, failures, witnesses, timings = 0, [], [], []
    start = time.perf_counter()
    for one in trees:
        t1 = Forest.tree(one)
        for two in trees:
            t2 = Forest.tree(two)
            f2 = t2.yielded({t2.children[0][0]})
            for a, c in combinations(('a', 'b', 'c', 'd'), 2):
                av, cv = f2.node(a), f2.node(c)
                u, path_edges, _ = f2.path(av, cv)
                if u in f2.parent:
                    continue
                sides = side_edges(f2, av, cv)
                if not sibling_pair(t1, f2.yielded(sides), a, c):
                    continue
                available = f2.edges - sides
                for extra in all_subsets(available):
                    cuts = sides | extra
                    if len(cuts & path_edges) < 2:
                        continue
                    if not af(f2.yielded(cuts), t1, t2)['ok']:
                        continue
                    row = inspect_case(t1, t2, t1, f2, [a, c], cuts, sides)
                    assert row['in_target_regime'] and not row['lca_parent_exists']
                    count += 1
                    if len(witnesses) < 3:
                        witnesses.append({'T1': one, 'T2': two, 'pair': [a, c], **row})
                    if not row['normalized_AF']['ok']:
                        failures.append({'T1': one, 'T2': two, 'pair': [a, c], **row})
                    if count % 10 == 0:
                        timings.append({'completed_valid_premises': count, 'seconds': time.perf_counter() - start})
                    if limit and count >= limit:
                        return {'tested': count, 'failures': failures, 'witnesses': witnesses,
                                'timings': timings, 'seconds': time.perf_counter() - start, 'exhaustive': False}
    return {'tested': count, 'failures': failures, 'witnesses': witnesses,
            'timings': timings, 'seconds': time.perf_counter() - start, 'exhaustive': True}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--stage', choices=['controls', 'pilot'], default='controls')
    parser.add_argument('--limit', type=int, default=40)
    args = parser.parse_args()
    start = time.perf_counter()
    stamp = datetime.now(timezone.utc).isoformat()
    result = {'schema_version': 1, 'started_at': stamp, 'stage': args.stage,
              'lineage': 'new component partitions, rooted restrictions, vertex-disjoint minimal embeddings; no code reuse'}
    result.update(replay_controls())
    if args.stage == 'pilot':
        result['compound_witness'] = compound_hunt()
        result['root_boundary'] = root_pilot(args.limit)
    result['elapsed_seconds'] = time.perf_counter() - start
    path = RESULTS / ('thesis-correctness-repair-component-' + args.stage + '.json')
    atomic(path, result)
    compound = result.get('compound_witness', {})
    fire = bool(compound.get('in_target_regime')) and not compound.get('normalized_AF', {'ok': True})['ok']
    root = result.get('root_boundary', {})
    atomic(PROGRESS, {'id': 'thesis-correctness-repair-component',
        'title': 'Independent component normalization adversary', 'status': 'running',
        'summary': 'Compound-subtree counterexample executed; requires fresh verification.' if fire else 'Frozen controls executed; component-route adversary in progress.',
        'metrics': {'controls_passed': len(result['controls']), 'negative_controls_caught': len(result['negative_controls']),
                    'valid_root_boundary_states': root.get('tested', 0), 'compound_counterexamples': int(fire), 'lean_theorems_checked': 0},
        'claims': [{'id': 'compound-normalization', 'label': 'Unrestricted compound normalization',
                    'status': 'refuted' if fire else 'open',
                    'detail': 'Executed exact witness satisfies active containment and AF compatibility but normalization fails; fresh nonauthor check pending.' if fire else 'Not yet tested.'},
                   {'id': 'atomic-normalization', 'label': 'Ordinary-leaf normalization', 'status': 'open',
                    'detail': 'Finite adversarial tests are not a universal proof.'}],
        'lemmas': [], 'artifacts': [str(path), str(ROUTE / 'evaluator.py'), str(ROUTE / 'ADVERSARY.md')]})
    print(json.dumps({'stage': args.stage, 'controls_passed': len(result['controls']),
                      'negative_controls_caught': len(result['negative_controls']),
                      'root_boundary_tested': root.get('tested', 0),
                      'compound_in_regime': compound.get('in_target_regime'),
                      'compound_normalized_AF': compound.get('normalized_AF', {}).get('ok'),
                      'seconds': result['elapsed_seconds'], 'receipt': str(path)}, sort_keys=True))


if __name__ == '__main__':
    main()
