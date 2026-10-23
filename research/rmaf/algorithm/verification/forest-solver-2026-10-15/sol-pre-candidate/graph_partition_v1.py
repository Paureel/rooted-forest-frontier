#!/usr/bin/env python3
"""One-shot prerelease review instrument, built fresh from public definitions.

Graph hulls use shortest paths in the original tree; restricted topologies use
clade sets. No RMAF/project evaluator code is imported. Exact integer/Fraction
arithmetic only. This enumerates finite fixtures, not a practical MAF solver.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent


class Graph:
    def __init__(self, tree):
        self.tree = tree
        self.adj = {}
        self.at = {}
        self.taxa = []
        self.desc = {}
        if tree is not None:
            self._build(tree, ())

    def _build(self, t, v):
        self.adj[v] = set()
        if isinstance(t, int):
            self.at[v] = t
            self.taxa.append(t)
            self.desc[v] = frozenset([t])
        else:
            if not isinstance(t, list) or len(t) != 2:
                raise ValueError('tree is an integer or a two-child list')
            ds = set()
            for side, child in enumerate(t):
                w = v + (side,)
                self._build(child, w)
                self.adj[v].add(w)
                self.adj[w].add(v)
                ds |= self.desc[w]
            self.desc[v] = frozenset(ds)

    def path(self, a, b):
        # Unique tree path, obtained by breadth-first predecessor search.
        todo = [a]
        pred = {a: None}
        for v in todo:
            if v == b:
                break
            for w in self.adj[v]:
                if w not in pred:
                    pred[w] = v
                    todo.append(w)
        if b not in pred:
            raise ValueError('disconnected graph')
        out = []
        v = b
        while v is not None:
            out.append(v)
            v = pred[v]
        return frozenset(out)

    def hull(self, labels):
        wanted = set(labels)
        vs = [v for v, x in self.at.items() if x in wanted]
        if not vs:
            return frozenset()
        out = {vs[0]}
        for v in vs[1:]:
            out |= self.path(vs[0], v)
        return frozenset(out)

    def topology(self, labels):
        wanted = frozenset(labels) & frozenset(self.taxa)
        if not wanted:
            return None
        # All clusters induced by original descendant sets. Unary vertices
        # generate repeated clusters and vanish in this set representation.
        clusters = {frozenset(ds & wanted) for ds in self.desc.values()}
        return wanted, frozenset(c for c in clusters if len(c) > 1)

    def restriction(self, labels):
        wanted = set(labels)
        if not self.hull(wanted):
            return None
        active = {v for v, ds in self.desc.items() if ds & wanted}

        def construct(v):
            if v in self.at:
                return self.at[v]
            children = sorted(w for w in self.adj[v]
                              if len(w) == len(v) + 1 and w in active)
            out = [construct(w) for w in children]
            return out[0] if len(out) == 1 else out
        return construct(())

    def disjoint(self, blocks):
        occupied = set()
        for b in blocks:
            h = self.hull(b)
            if occupied & h:
                return False
            occupied |= h
        return True

    def regions(self, vertex, selected=None):
        vertex = tuple(vertex)
        if vertex not in self.adj or vertex in self.at:
            raise ValueError('selected vertex must be original nonleaf')
        wanted = set(self.taxa if selected is None else selected)
        regions = []
        for neighbor in sorted(self.adj[vertex]):
            seen = {vertex}
            todo = [neighbor]
            labs = set()
            for v in todo:
                if v in seen:
                    continue
                seen.add(v)
                if v in self.at and self.at[v] in wanted:
                    labs.add(self.at[v])
                todo.extend(w for w in self.adj[v] if w not in seen)
            if labs:
                regions.append(sorted(labs))
        return sorted(regions)

    def cut_components(self, removed_child_addresses):
        banned = {frozenset([tuple(w), tuple(w)[:-1]])
                  for w in removed_child_addresses}
        seen = set()
        leafless = 0
        out = []
        for start in self.adj:
            if start in seen:
                continue
            todo = [start]
            labs = []
            for v in todo:
                if v in seen:
                    continue
                seen.add(v)
                if v in self.at:
                    labs.append(self.at[v])
                todo.extend(w for w in self.adj[v] if w not in seen
                            and frozenset([v, w]) not in banned)
            if labs:
                out.append(sorted(labs))
            else:
                leafless += 1
        return sorted(out), leafless


def partition_ok(labels, blocks):
    flat = [x for b in blocks for x in b]
    return all(blocks) and Counter(flat) == Counter(labels) and len(set(labels)) == len(labels)


def partitions(labels):
    # Unique set partitions from a first-element insertion recurrence.
    labels = sorted(labels)
    if not labels:
        yield []
        return
    first, *rest = labels
    for p in partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i+1:]


class State:
    def __init__(self, target, sources):
        self.T = Graph(target)
        self.ss = [Graph(s) for s in sources]
        flat = [x for g in self.ss for x in g.taxa]
        self.proper = (len(set(self.T.taxa)) == len(self.T.taxa)
                       and Counter(flat) == Counter(self.T.taxa)
                       and len(flat) == len(set(flat)))

    def agrees(self, forest, drop_overlap=False):
        if not self.proper or not partition_ok(self.T.taxa, forest):
            return False
        owners = []
        for b in forest:
            os = [i for i, s in enumerate(self.ss) if set(b) <= set(s.taxa)]
            if len(os) != 1:
                return False
            owners.append(os[0])
        if not drop_overlap and not self.T.disjoint(forest):
            return False
        for i, s in enumerate(self.ss):
            local = [b for b, o in zip(forest, owners) if o == i]
            if not partition_ok(s.taxa, local) or not s.disjoint(local):
                return False
            if any(self.T.topology(b) != s.topology(b) for b in local):
                return False
        return True

    def forests(self):
        if self.proper:
            yield from (f for f in partitions(self.T.taxa) if self.agrees(f))

    def exact(self):
        valid = list(self.forests())
        if not valid:
            return None, []
        minimum = min(len(f) - len(self.ss) for f in valid)
        return minimum, valid

    def current_disjoint(self):
        return self.T.disjoint([s.taxa for s in self.ss])


def equal(actual, expected, site):
    if actual != expected:
        raise AssertionError(json.dumps({'site': site, 'actual': actual,
                                         'expected': expected}, default=str))


def expect_caught(name, action):
    try:
        action()
    except (AssertionError, ValueError):
        return {'plant': name, 'caught': True}
    raise AssertionError('SURVIVING FALSE PLANT: ' + name)


def mass(rows, c):
    return sum((c ** (-r['d']) for r in rows), Fraction(0))


def raw_gate(actual, expected):
    equal(Counter((r['id'], r['d']) for r in actual),
          Counter((r['id'], r['d']) for r in expected), 'raw occurrence multiset')


def controls(spec):
    literals = spec['control_literals']
    crossed = spec['cases'][0]
    state = State(crossed['T'], crossed['ss'])
    rows = []
    equal(state.agrees(crossed['witness']), True, 'known witness')
    equal(state.exact()[0], 1, 'known minimum')
    rows.append({'known_plant':'crossed q1 witness and min', 'passed':True})
    false_forest = literals['forged_agreement']['forest']
    equal(state.agrees(false_forest, drop_overlap=True), True, 'topology-only twin')
    equal(state.agrees(false_forest), False, 'literal overlap twin')
    rows.append(expect_caught('drop_target_overlap', lambda: equal(
        state.agrees(false_forest, drop_overlap=True), state.agrees(false_forest), 'overlap')))
    rows.append(expect_caught('forged_target_agreement', lambda: equal(
        state.agrees(false_forest), True, 'forged agreement')))
    rows.append(expect_caught('ordinary_offset', lambda: equal(
        len(crossed['witness'])-1, crossed['minimum'], 'component offset')))
    for key in ['absent_label_restriction', 'mixed_absent_restriction']:
        f = literals[key]
        equal(Graph(f['tree']).restriction(f['selected']), f['expected'], key)
    rows.append(expect_caught('absent_label_leaf', lambda: equal(
        Graph([11,37]).restriction([103]), 103, 'absent label')))
    f = literals['suppressed_vertex']
    g = Graph(f['T'])
    v = tuple(f['kept_original_vertex'])
    h = g.hull(f['labels'])
    equal(v in h, True, 'unsuppressed hull ownership')
    equal(len(g.adj[v] & h), f['degree_in_hull'], 'suppressed vertex degree')
    equal(v in g.hull(f['other_labels']), True, 'other hull ownership')
    rows.append(expect_caught('suppressed_vertex_discard', lambda: equal(
        len(g.adj[v] & h) != 2, True, 'discard suppressed vertex')))
    f = literals['leafless_cut']
    bs, n = Graph(f['tree']).cut_components(f['removed_edges'])
    equal([bs,n], [f['nonempty_blocks'], f['leafless_components']], 'leafless cut')
    rows.append(expect_caught('edge_count_equals_component_cost', lambda: equal(
        len(f['removed_edges']), f['additional_cost'], 'edge vs component count')))
    f = literals['replace_only']
    replacement = [Graph(f['ss'][f['parent_index']]).restriction(b) for b in f['blocks']]
    actual = f['ss'][:f['parent_index']] + replacement + f['ss'][f['parent_index']+1:]
    equal(actual, f['expected_sources'], 'replace only parent')
    equal(len(actual)-len(f['ss']), f['component_change'], 'replacement delta')
    rows.append(expect_caught('erased_other_source', lambda: equal(
        replacement, f['expected_sources'], 'erase other source')))
    allowed = [literals['incomplete_cover']['only_allowed_forest']]
    affordable = any(state.agrees(f) and len(f)-len(state.ss) <= 1 for f in allowed)
    equal(affordable, False, 'incomplete cover fixture')
    rows.append(expect_caught('incomplete_branch_cover', lambda: equal(
        affordable, True, 'coverage at q1')))
    raw = literals['raw_occurrences']
    raw_gate(raw, raw)
    equal(str(mass(raw, Fraction(2))), literals['raw_mass_c2'], 'all raw mass')
    rows.append(expect_caught('missing_raw_occurrence', lambda: raw_gate(raw[1:], raw)))
    rows.append(expect_caught('duplicate_raw_occurrence', lambda: raw_gate(raw+[raw[0]], raw)))
    for c, key in [(Fraction(2),'mass_c2'), (Fraction(3),'mass_c3')]:
        equal(str(mass(literals['mass_bound_two_source_fixture'],c)), literals[key], key)
    raw2 = literals['false_below_c2_fixture']
    equal(mass(raw2,Fraction(2)) <= 1, True, 'fixture bound at c2')
    m = mass(raw2,Fraction(3,2))
    equal(str(m), literals['false_below_c2_mass'], 'sub2 mass')
    rows.append(expect_caught('false_mass_below_c2', lambda: equal(m <= Fraction(4,3), True,'false sub2 bound')))
    f = literals['discount']
    equal(f['query_actual_cost']+f['next_query_minimum'], f['true_total'], 'actual query charges')
    rows.append(expect_caught('own_minimum_discount', lambda: equal(
        f['false_own_minimum_total'],f['true_total'],'discount')))
    f = literals['bill']
    costs = {k:v for k,v in f.items() if k != 'expected_total'}
    equal(sum(costs.values()),f['expected_total'],'complete bill')
    for key in ['prefix','refusal','materialization','list_copy']:
        rows.append(expect_caught('unpaid_'+key, lambda key=key: equal(
            sum(v for k,v in costs.items() if k != key), f['expected_total'], 'missing bill '+key)))
    # An ordinary table is a literal mock fixture, never an implementation IH.
    table = literals['ordinary_table']
    for budget, answer in zip(table['budgets'], table['answer']):
        equal(answer is not None, budget >= table['minimum'], 'mock exact table')
    equal(sorted(r['plant'] for r in rows if 'plant' in r),
          sorted(spec['false_twins_required']), 'plant denominator')
    return rows


def run_case(case, supplement):
    start = time.perf_counter()
    state = State(case['T'],case['ss'])
    equal(state.proper,case['proper'],case['id']+' proper')
    if not state.proper:
        equal(state.exact(),(None,[]),case['id']+' refusal')
        return {'id':case['id'],'proper':False,'seconds':time.perf_counter()-start}
    expected = {**case, **(supplement['three_region'] if case['id']=='three_region' else {})}
    minimum, valid = state.exact()
    equal(minimum,expected['minimum'],case['id']+' minimum')
    equal(state.agrees(expected['witness']),True,case['id']+' witness')
    equal(len(expected['witness']),expected['blocks'],case['id']+' witness blocks')
    equal(state.current_disjoint(),case['whole_target_disjoint'],case['id']+' current hulls')
    outcomes = [any(len(f)-len(state.ss) <= q for f in valid) for q in expected['budgets']]
    equal(outcomes,expected['affordable'],case['id']+' budgets')
    # Universal ownership/readout, not only an optimum, at the pinned vertex.
    owner_checks = 0
    if case['id'] == 'three_region':
        equal(state.T.regions(case['selected_vertex']),case['regions'],'three target regions')
        for s, rs in zip(state.ss,case['source_regions']):
            equal(state.T.regions(case['selected_vertex'],s.taxa),rs,'source regions')
        v = tuple(case['selected_vertex'])
        for forest in valid:
            occupied = []
            for source in state.ss:
                local = [b for b in forest if set(b) <= set(source.taxa)]
                hits = [b for b in local if v in state.T.hull(b)]
                occupied.append(bool(hits))
                if not hits:
                    rs = [set(r) for r in state.T.regions(v,source.taxa)]
                    equal(all(any(set(b) <= r for r in rs) for b in local),True,'ownership monochromatic readout')
            equal(sum(occupied) <= 1,True,'selected vertex ownership')
            owner_checks += 1
    return {'id':case['id'],'proper':True,'minimum':minimum,'valid_forests':len(valid),
            'partitions':sum(1 for _ in partitions(state.T.taxa)), 'budgets':expected['budgets'],
            'affordable':outcomes,'ownership_checks':owner_checks,'seconds':time.perf_counter()-start}


def metamorphisms(spec, supplement):
    rows = []
    def relabel(t, f):
        return f(t) if isinstance(t,int) else [relabel(t[1],f),relabel(t[0],f)]
    for case in spec['cases'][:3]:
        state = State(case['T'],case['ss'])
        m, valid = state.exact()
        for index, sources in enumerate([case['ss'],list(reversed(case['ss']))]):
            for f in [lambda x:37*x+11,lambda x:-19*x-7]:
                other = State(relabel(case['T'],f),[relabel(s,f) for s in sources])
                equal(other.exact()[0],m,'relabel/source order')
                checks = 0
                for forest in valid:
                    changed = [[f(x) for x in reversed(b)] for b in reversed(forest)]
                    equal(other.agrees(changed),True,'block/label/source/sibling permutation')
                    checks += 1
                rows.append({'id':case['id'],'source_permutation':index,'labels':other.T.taxa,
                             'minimum':m,'forests_rechecked':checks,'negative_labels_extended_only':any(x<0 for x in other.T.taxa)})
    return rows


def main():
    p = argparse.ArgumentParser()
    p.add_argument('mode',choices=['plants','pilot','battery'])
    p.add_argument('--out',required=True)
    args=p.parse_args()
    spec=json.loads((HERE/'EXPECTATIONS-v1.json').read_text())
    supplement=json.loads((HERE/'EXPECTATIONS-v2-supplement.json').read_text())
    result={'mode':args.mode,'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
            'fresh_code':True,'candidate_contact':False,'claims':'finite fixture checks only'}
    try:
        if args.mode=='plants':
            result['controls']=controls(spec)
        else:
            cases=spec['cases'][:2] if args.mode=='pilot' else spec['cases']
            result['cases']=[run_case(case,supplement) for case in cases]
            if args.mode=='battery':
                result['partition_counts']={str(n):sum(1 for _ in partitions(list(range(n)))) for n in range(7)}
                equal(result['partition_counts'],supplement['literal_partition_counts'],'Bell denominator')
                result['metamorphisms']=metamorphisms(spec,supplement)
        result['passed']=True
    except Exception as exc:
        result['passed']=False
        result['failure']=str(exc)
        Path(args.out).write_text(json.dumps(result,indent=2)+'\n')
        raise
    Path(args.out).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'mode':args.mode,'passed':result['passed'],
                      'cases':len(result.get('cases',[])),'controls':len(result.get('controls',[])),
                      'receipt':args.out}))


if __name__=='__main__':
    main()
