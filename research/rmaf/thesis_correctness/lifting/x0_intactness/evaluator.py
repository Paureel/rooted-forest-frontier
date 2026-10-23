#!/usr/bin/env python3
"""One-shot independent X0 instrument, 2026-10-14; standard library only.
Enumerate actual edge-deletion sets; AF by equality of exact cut/yield images.
This audit implementation intentionally imports no existing RMAF evaluator.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import argparse
import hashlib
import json
import os
import time

ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
CONTROLS = HERE.parent / 'controls.json'
RESULTS = ROOT / 'results'

@dataclass
class Forest:
    vertices: tuple
    labels: dict
    edges: tuple

    @classmethod
    def from_tree(cls, tree, rho=True):
        vertices, labels, edges = [], {}, []
        def add(t):
            v = len(vertices); vertices.append(v)
            if isinstance(t, str):
                labels[v] = t
            else:
                assert len(t) == 2
                for child in t:
                    w = add(child); edges.append((f'e{len(edges)}', v, w))
            return v
        if rho:
            vertices.append(0); labels[0] = 'rho'
            r = add(tree); edges.append((f'e{len(edges)}', 0, r))
        else:
            add(tree)
        f = cls(tuple(vertices), labels, tuple(edges)); f.validate(); return f

    @classmethod
    def from_signature(cls, signature):
        vertices, labels, edges = [], {}, []
        def add(t):
            label, children = t
            v = len(vertices); vertices.append(v)
            if label: labels[v] = label
            for child in children:
                w = add(child); edges.append((f'e{len(edges)}', v, w))
            return v
        for t in signature: add(t)
        f = cls(tuple(vertices), labels, tuple(edges)); f.validate(); return f

    def validate(self):
        assert len(self.labels.values()) == len(set(self.labels.values()))
        incoming, children = {}, {v: [] for v in self.vertices}
        for eid, p, c in self.edges:
            assert c not in incoming and p in children and c in children
            incoming[c] = p; children[p].append(c)
        assert len({e[0] for e in self.edges}) == len(self.edges)
        visited = set()
        def walk(v):
            assert v not in visited; visited.add(v)
            for c in children[v]: walk(c)
        for v in self.vertices:
            if v not in incoming: walk(v)
        assert visited == set(self.vertices)
        for v in self.vertices:
            if v not in self.labels: assert len(children[v]) == 2
            elif self.labels[v] == 'rho': assert v not in incoming and len(children[v]) <= 1
            else: assert not children[v]
        return True

    def yielded(self, cuts=frozenset()):
        incoming, children = {}, {v: [] for v in self.vertices}
        for eid, p, c in self.edges:
            if eid not in cuts:
                incoming[c] = p; children[p].append(c)
        empty_components = []
        def reduce(v):
            subtrees = [reduce(c) for c in children[v]]
            subtrees = tuple(sorted((t for t in subtrees if t is not None), key=repr))
            if v in self.labels: return (self.labels[v], subtrees)
            if not subtrees: return None
            if len(subtrees) == 1: return subtrees[0]
            return ('', subtrees)
        forest = []
        def descendants(v):
            return [v] + [w for c in children[v] for w in descendants(c)]
        for v in self.vertices:
            if v not in incoming:
                t = reduce(v)
                if t is None: empty_components.append(descendants(v))
                else: forest.append(t)
        return tuple(sorted(forest, key=repr)), empty_components

    def clusters(self):
        children = {v: [] for v in self.vertices}
        for _, p, c in self.edges: children[p].append(c)
        def desc(v):
            labels = {self.labels[v]} if v in self.labels else set()
            for c in children[v]: labels.update(desc(c))
            return frozenset(labels)
        return {eid: desc(c) for eid, _, c in self.edges}

    def cuts_for_clusters(self, clusters):
        lookup = {labels: eid for eid, labels in self.clusters().items()}
        return frozenset(lookup[frozenset(c)] for c in clusters)

    def cut_clusters(self, cuts):
        cs = self.clusters()
        return sorted([sorted(cs[e]) for e in cuts])

    def internal_edges(self, labels):
        labels = frozenset(labels)
        return frozenset(eid for eid, cl in self.clusters().items() if cl < labels)

    def proper_subtrees(self):
        incoming = {c: p for _, p, c in self.edges}
        children = {v: [] for v in self.vertices}
        for _, p, c in self.edges: children[p].append(c)
        def sig(v): return (self.labels.get(v, ''), tuple(sorted((sig(c) for c in children[v]), key=repr)))
        def lab(t): return frozenset(([t[0]] if t[0] else []) + [x for c in t[1] for x in lab(c)])
        result = {}
        for v in incoming:
            t = sig(v); ls = lab(t)
            if len(ls) >= 2 and 'rho' not in ls: result[ls] = t
        return result

    def contracted(self, labels, alpha='alpha'):
        labels = frozenset(labels)
        def lab(t): return frozenset(([t[0]] if t[0] else []) + [x for c in t[1] for x in lab(c)])
        def replace(t):
            if lab(t) == labels: return (alpha, ())
            return (t[0], tuple(sorted((replace(c) for c in t[1]), key=repr)))
        return Forest.from_signature(tuple(sorted((replace(t) for t in self.yielded()[0]), key=repr)))

    def record(self):
        return {'vertices': list(self.vertices), 'labels': self.labels, 'edges': self.edges,
                'signature': self.yielded()[0]}


def all_cutsets(f):
    ids = [e[0] for e in f.edges]
    for k in range(len(ids)+1):
        for subset in combinations(ids, k): yield frozenset(subset)


def image(f):
    outputs = {}
    for cuts in all_cutsets(f):
        signature, empty = f.yielded(cuts)
        outputs.setdefault(signature, []).append(cuts)
    return outputs


def enumerate_af(f1, f2, force=frozenset()):
    images1 = image(f1)
    accepted = []
    for cuts in all_cutsets(f2):
        if not force <= cuts: continue
        signature, empty = f2.yielded(cuts)
        if signature in images1:
            accepted.append({'cuts': cuts, 'signature': signature,
                             'empty_components': empty, 'witness_F1_cuts': images1[signature][0]})
    assert accepted, 'All-singleton feasibility unexpectedly absent'
    optimum = min(len(x['cuts']) for x in accepted)
    return optimum, [x for x in accepted if len(x['cuts']) == optimum], accepted


def actual_minimum_summary(f1, f2, labels=None, force=frozenset()):
    optimum, minima, accepted = enumerate_af(f1, f2, force)
    result = {'optimum': optimum, 'minimum_cut_clusters': sorted([f2.cut_clusters(x['cuts']) for x in minima]),
              'minimum_count': len(minima), 'accepted_cutsets': len(accepted),
              'all_minima': [dict(x, cuts=sorted(x['cuts']), witness_F1_cuts=sorted(x['witness_F1_cuts'])) for x in minima]}
    if labels:
        internal = f2.internal_edges(labels)
        intact = [not (x['cuts'] & internal) for x in minima]
        result.update(every_minimum_intact=all(intact), exists_minimum_intact=any(intact),
                      internal_edges=sorted(internal), violating_minimum_count=sum(not x for x in intact))
    return result


def mismatch(expected, actual): return expected != actual


def run_control(c):
    f1, f2 = Forest.from_tree(c['T1']), Forest.from_tree(c['T2'])
    result = {'id': c['id'], 'F1': f1.record(), 'F2': f2.record(), 'comparisons': []}
    def check(key, actual):
        expected = c['expected_'+key]
        bad = mismatch(expected, actual)
        assert mismatch(expected, {'deliberately_wrong': actual}), 'Comparator mutation not caught'
        result['comparisons'].append({'key': key, 'expected': expected, 'actual': actual, 'pass': not bad,
                                      'mutation_caught': True})
    if 'common_subtree_labels' in c:
        labels = c['common_subtree_labels']
        summary = actual_minimum_summary(f1, f2, labels)
        result['exact'] = summary
        for key in ('optimum','minimum_cut_clusters','every_minimum_intact','exists_minimum_intact'):
            if 'expected_'+key in c: check(key, summary[key])
        if 'expected_contracted_optimum' in c:
            q1,q2 = f1.contracted(labels), f2.contracted(labels)
            check('contracted_optimum', actual_minimum_summary(q1,q2)['optimum'])
            result['contracted_graphs'] = [q1.record(), q2.record()]
            result['specified_contracted_inputs_match'] = q1.yielded()[0] == Forest.from_tree(c['contracted_T1']).yielded()[0] and q2.yielded()[0] == Forest.from_tree(c['contracted_T2']).yielded()[0]
            assert result['specified_contracted_inputs_match']
    elif 'cut_clusters' in c:
        cuts = f2.cuts_for_clusters(c['cut_clusters']); opt, minima, accepted = enumerate_af(f1,f2)
        check('AF', any(x['cuts']==cuts for x in accepted))
        check('intact', not bool(cuts & f2.internal_edges(['a','b'])))
        check('minimum', len(cuts)==opt)
    elif 'forced_cut_clusters' in c:
        cuts = f2.cuts_for_clusters(c['forced_cut_clusters'])
        base = actual_minimum_summary(f1,f2,['a','b'])
        forced = actual_minimum_summary(f1,f2,['a','b'],cuts)
        result['unrestricted'], result['forced'] = base, forced
        check('unrestricted_optimum', base['optimum'])
        check('forced_extension_optimum', forced['optimum'])
        check('forced_minimum_intact', forced['every_minimum_intact'])
    elif 'C_clusters' in c:
        cuts = f2.cuts_for_clusters(c['C_clusters'])
        opt, minima, _ = enumerate_af(f1,f2)
        residual = Forest.from_signature(f2.yielded(cuts)[0])
        residual_opt = actual_minimum_summary(f1,residual)['optimum']
        result['C'], result['residual'] = sorted(cuts), residual.record()
        check('unrestricted_optimum', opt)
        check('residual_optimum', residual_opt)
        check('C_plus_residual_optimum', len(cuts)+residual_opt)
        check('C_contained_in_any_global_minimum', any(cuts <= x['cuts'] for x in minima))
    elif 'candidate_common_labels' in c:
        ls = frozenset(c['candidate_common_labels'])
        sub1,sub2 = f1.proper_subtrees(),f2.proper_subtrees()
        check('identical_pendant_subtree', ls in sub1 and ls in sub2 and sub1[ls]==sub2[ls])
    else: raise ValueError(c)
    result['pass'] = all(x['pass'] for x in result['comparisons'])
    return result


def run_controls(path):
    start=time.perf_counter(); controls=json.loads(CONTROLS.read_text())
    receipt={'control_version':controls['version'],'control_sha256':hashlib.sha256(CONTROLS.read_bytes()).hexdigest(),
             'evaluator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             'controls':[], 'search_executed':False}
    for c in controls['minimum_controls']:
        result=run_control(c); receipt['controls'].append(result)
        receipt['passed']=sum(x['pass'] for x in receipt['controls'])
        receipt['executed']=len(receipt['controls']); receipt['elapsed_seconds']=time.perf_counter()-start
        receipt['status']='passed' if result['pass'] else 'STOP_CONTROL_MISMATCH'
        path.write_text(json.dumps(receipt,indent=2)+'\n')
        print(c['id'], 'PASS' if result['pass'] else 'STOP_CONTROL_MISMATCH', flush=True)
        if not result['pass']: return False
    return True

if __name__ == '__main__':
    p=argparse.ArgumentParser(); p.add_argument('--receipt',type=Path,required=True)
    args=p.parse_args()
    raise SystemExit(0 if run_controls(args.receipt) else 2)
