#!/usr/bin/env python3
"""One-shot GLOBAL-C finite oracle; not a proposed safe-cover algorithm.

Fresh implementation from SPEC.md, stdlib only. Enumerates original source
cutsets and, separately, leaf partitions. Shared Tree primitives are explicitly
not independent verification. Toolkit consultation is recorded in SPEC.md.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools as it
import json
import random
from pathlib import Path
from time import perf_counter
from datetime import datetime, timezone


def canonical(t):
    if t is None or isinstance(t, str):
        return t
    return tuple(sorted((canonical(t[0]), canonical(t[1])), key=repr))


class Tree:
    def __init__(self, t):
        self.t = canonical(t)
        self.parent = {}
        self.children = {}
        self.leaf = {}
        self.edge = {}
        self.edges = []
        def visit(x, par=None):
            v = len(self.parent)
            self.parent[v] = par
            self.children[v] = []
            if par is not None:
                self.edge[v] = len(self.edges)
                self.edges.append((par, v))
                self.children[par].append(v)
            if isinstance(x, str):
                if x in self.leaf:
                    raise ValueError('duplicate label')
                self.leaf[x] = v
            else:
                for child in x:
                    visit(child, v)
            return v
        if t is not None:
            visit(self.t)
        self.labels = tuple(sorted(self.leaf))
        self._paths = {}
        for a, b in it.combinations(self.labels, 2):
            self._paths[frozenset((a, b))] = self.path(a, b)

    def path(self, a, b):
        av, bv = self.leaf[a], self.leaf[b]
        aa = []
        while av is not None:
            aa.append(av)
            av = self.parent[av]
        bb = []
        while bv not in aa:
            bb.append(bv)
            bv = self.parent[bv]
        aa = aa[:aa.index(bv)+1]
        vertices = frozenset(aa + bb)
        edges = 0
        for v in vertices:
            if self.parent[v] in vertices:
                edges |= 1 << self.edge[v]
        return vertices, edges

    def support(self, labels):
        labels = tuple(labels)
        if len(labels) == 1:
            return frozenset((self.leaf[labels[0]],))
        out = set()
        for a, b in it.combinations(labels, 2):
            out.update(self._paths[frozenset((a, b))][0])
        return frozenset(out)

    def span_edges(self, labels):
        mask = 0
        for a, b in it.combinations(labels, 2):
            mask |= self._paths[frozenset((a, b))][1]
        return mask

    def restrict(self, labels):
        labels = frozenset(labels)
        def walk(t):
            if t is None:
                return None
            if isinstance(t, str):
                return t if t in labels else None
            a, b = map(walk, t)
            if a is None:
                return b
            if b is None:
                return a
            return canonical((a, b))
        return walk(self.t)

    def cut_partition(self, mask):
        seen, blocks = set(), []
        vertex_label = {v: a for a, v in self.leaf.items()}
        neighbors = {v: [] for v in self.parent}
        for i, (u, v) in enumerate(self.edges):
            if not mask & (1 << i):
                neighbors[u].append(v)
                neighbors[v].append(u)
        for v in self.parent:
            if v in seen:
                continue
            stack, labels = [v], []
            seen.add(v)
            while stack:
                w = stack.pop()
                if w in vertex_label:
                    labels.append(vertex_label[w])
                for u in neighbors[w]:
                    if u not in seen:
                        seen.add(u)
                        stack.append(u)
            if labels:
                blocks.append(tuple(sorted(labels)))
        return tuple(sorted(blocks))

    def edge_receipt(self, mask):
        def descendants(v):
            stack, out = [v], []
            vl = {v: a for a, v in self.leaf.items()}
            while stack:
                u = stack.pop()
                if u in vl:
                    out.append(vl[u])
                stack.extend(self.children[u])
            return sorted(out)
        return [{'edge':i,'parent':u,'child':v,'child_labels':descendants(v)}
                for i,(u,v) in enumerate(self.edges) if mask & (1 << i)]


def partitions(labels):
    if not labels:
        yield ()
        return
    first, rest = labels[0], labels[1:]
    for p in partitions(rest):
        yield tuple(sorted(((first,),) + p))
        for i in range(len(p)):
            yield tuple(sorted(p[:i] + (tuple(sorted((first,) + p[i])),) + p[i+1:]))


def agreement(S, T, part):
    if tuple(sorted(a for b in part for a in b)) != S.labels or S.labels != T.labels:
        return False
    used_s, used_t = set(), set()
    for block in part:
        if not block or S.restrict(block) != T.restrict(block):
            return False
        ss, st = S.support(block), T.support(block)
        if used_s & ss or used_t & st:
            return False
        used_s.update(ss)
        used_t.update(st)
    return True


def part_cost(p):
    return max(0, len(p)-1)


def oracle(S, T):
    good = [p for p in partitions(S.labels) if agreement(S, T, p)]
    value = min(map(part_cost, good))
    return value, tuple(p for p in good if part_cost(p) == value), good


def conflicts(S, T):
    rows = {}
    for triple in it.combinations(S.labels, 3):
        if S.restrict(triple) != T.restrict(triple):
            mask = S.span_edges(triple)
            rows.setdefault(mask, []).append({'kind':'triple','labels':triple})
    for quartet in it.combinations(S.labels, 4):
        a, b, c, d = quartet
        for p, q in [((a,b),(c,d)), ((a,c),(b,d)), ((a,d),(b,c))]:
            sp, ep = S._paths[frozenset(p)]
            sq, eq = S._paths[frozenset(q)]
            tp, _ = T._paths[frozenset(p)]
            tq, _ = T._paths[frozenset(q)]
            if not sp & sq and tp & tq:
                rows.setdefault(ep | eq, []).append({'kind':'path-overlap','pairs':[p,q]})
    return rows


def packing(hyperedges):
    # Exact maximum disjoint packing, finite oracle only.
    states = {0: ()}
    for h in sorted(hyperedges):
        for used, selected in list(states.items()):
            if not used & h:
                new = used | h
                candidate = selected + (h,)
                if len(candidate) > len(states.get(new, ())):
                    states[new] = candidate
    return max(states.values(), key=len)


def refine(p, f):
    return all(any(set(block) <= set(big) for big in f) for block in p)


def exact_row(source, target, precut_blocks=None, retain=False):
    start = perf_counter()
    S, T = Tree(source), Tree(target)
    if S.labels != T.labels:
        raise ValueError('source/target label mismatch')
    opt, opts, good = oracle(S, T)
    H = conflicts(S, T)
    pack = packing(H)
    hitting_opt = len(S.edges) + 1
    tested = 0
    optimal_masks = []
    for c in range(1 << len(S.edges)):
        hit = all(c & h for h in H)
        p = S.cut_partition(c)
        valid = agreement(S, T, p)
        tested += 1
        if hit != valid:
            raise AssertionError({'source':source,'target':target,'cuts':S.edge_receipt(c),
                                  'partition':p,'hits':hit,'agreement':valid,'conflicts':H})
        if hit:
            cost = c.bit_count()
            if cost < hitting_opt:
                hitting_opt, optimal_masks = cost, [c]
            elif cost == hitting_opt:
                optimal_masks.append(c)
    assert hitting_opt == opt, ('hitting minimum vs partition minimum', hitting_opt, opt)
    out = {'optimum':opt,'packing':len(pack),'hyperedge_count':len(H),
           'cutsets_tested':tested,'partition_optimum_count':len(opts),
           'minimum_hitting_masks':optimal_masks,'seconds':perf_counter()-start}
    if retain:
        out.update(optimum_partitions=opts, source_edges=S.edge_receipt((1 << len(S.edges))-1),
                   conflicts=[{'edge_mask':h,'edges':S.edge_receipt(h),'causes':causes} for h,causes in H.items()],
                   maximum_disjoint_packing=pack)
    if precut_blocks is not None:
        f = tuple(sorted(tuple(sorted(b)) for b in precut_blocks))
        realizations = [c for c in range(1 << len(S.edges)) if S.cut_partition(c) == f
                        and c.bit_count() == part_cost(f)]
        assert realizations, 'precut partition is not source-realizable at nonredundant cost'
        survivors = [p for p in opts if refine(p, f)]
        finals = [p for p in good if refine(p, f)]
        completion = min(len(p)-len(f) for p in finals)
        tau = max((oracle(Tree(S.restrict(b)),Tree(T.restrict(b)))[0] for b in f), default=0)
        out.update(precuts=part_cost(f),surviving=len(survivors),completion=completion,
                   tau=tau,charged=part_cost(f)+completion,
                   precut_realizations=[S.edge_receipt(c) for c in realizations])
    return out


def trees(labels):
    labels = tuple(labels)
    if len(labels) == 1:
        return (labels[0],)
    out = []
    for k in range(1, len(labels)):
        for left in it.combinations(labels[1:], k-1):
            a = (labels[0],) + left
            b = tuple(x for x in labels if x not in a)
            for x in trees(a):
                for y in trees(b):
                    out.append(canonical((x,y)))
    return tuple(sorted(set(out), key=repr))


def run_controls(path):
    frozen = json.loads(path.read_text())
    rows, mutations = [], []
    for fixture in frozen['fixtures']:
        out = exact_row(fixture['source'], fixture['target'], fixture.get('precut_blocks'), retain=True)
        checks = []
        for k, expected in fixture.items():
            if k.startswith('expected_'):
                actual = out[k.removeprefix('expected_')]
                checks.append({'field':k,'expected':expected,'actual':actual,'passed':actual == expected})
                assert actual == expected, (fixture['id'],k,expected,actual)
                corrupt = expected + 1
                caught = actual != corrupt
                assert caught
                mutations.append({'id':fixture['id'],'field':k,'corrupt':corrupt,'caught':caught})
        rows.append({'id':fixture['id'],'actual':out,'checks':checks})
    # Explicit corruption detection alongside clean singleton-cut twin.
    S, T = Tree((('a','b'),'c')), Tree((('a','c'),'b'))
    assert not agreement(S,T,(('a','b','c'),))
    assert agreement(S,T,(('a',),('b','c')))
    mutations.append({'id':'wrong-topology-unsplit','caught':True,'clean_twin':True})
    E = next(r['actual'] for r in rows if r['id'] == 'equal-half-survival-failure')
    C = next(r['actual'] for r in rows if r['id'] == 'equal-half-clean-twin')
    assert E['charged'] != E['completion'] and C['charged'] == C['optimum']
    mutations.append({'id':'wrong-precut-charge','caught':True,'clean_twin':True})
    whole = exact_row(['a',['b',['c','d']]],['a',[['b','c'],'d']], [['a','b','c','d']])
    assert 2*whole['tau'] > 1 and 2*E['tau'] <= 1
    mutations.append({'id':'false-halfbudget','caught':True,'clean_twin':True})
    return {'kind':'GLOBAL-C-frozen-controls','started_utc':datetime.now(timezone.utc).isoformat(),
            'controls_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'lineage':'fresh stdlib code; cut-mask vs partition enumeration; shared Tree primitives; no X0/production imports',
            'rows':rows,'mutations':mutations,'fixtures_passed':len(rows),
            'comparisons_passed':sum(len(r['checks']) for r in rows),
            'mutation_catches':len(mutations),'verdict':'FINITE-CONTROLS-REPRODUCE'}


def census(nmax, limit=None, sample=False):
    result = {'kind':'GLOBAL-C-conflict-characterization-census',
              'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'started_utc':datetime.now(timezone.utc).isoformat(),'sizes':[],
              'sampling':{'randomized':sample,'pair_limit_per_size':limit,
                          'seed_by_size':'20261015+n' if sample else None},
              'qualification':'finite tests do not close universal C1 or the safe-cover target',
              'smallest_packing_gap':None}
    for n in range(1,nmax+1):
        ts = trees(tuple(chr(97+i) for i in range(n)))
        started = perf_counter()
        count, checks, gaps, hist, timings = 0, 0, 0, {}, []
        pairlist = list(it.product(ts, repeat=2))
        if sample:
            random.Random(20261015+n).shuffle(pairlist)
        for s,t in pairlist:
            out = exact_row(s,t)
            count += 1
            checks += out['cutsets_tested']
            timings.append(out['seconds'])
            hist[str((out['packing'],out['optimum']))] = hist.get(str((out['packing'],out['optimum'])),0)+1
            if out['packing'] < out['optimum']:
                gaps += 1
                if result['smallest_packing_gap'] is None:
                    result['smallest_packing_gap'] = {'n':n,'source':s,'target':t,
                                                      'exact':exact_row(s,t,retain=True)}
            if limit is not None and count >= limit:
                break
        row = {'n':n,'tree_count':len(ts),'ordered_pair_count':len(ts)**2,
               'finished_pairs':count,'cutsets_checked':checks,'mismatches':0,
               'packing_gap_pairs':gaps,'packing_optimum_histogram':hist,
               'seconds':perf_counter()-started,'per_pair_seconds':timings}
        result['sizes'].append(row)
        print(json.dumps({k:v for k,v in row.items() if k != 'per_pair_seconds'}),flush=True)
    result['finished_utc'] = datetime.now(timezone.utc).isoformat()
    result['verdict'] = 'FINITE-CHARACTERIZATION-CLEAN; PACKING-TIGHTNESS-REFUTED' if result['smallest_packing_gap'] else 'FINITE-CHARACTERIZATION-CLEAN'
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--controls', type=Path)
    ap.add_argument('--census',type=int)
    ap.add_argument('--limit',type=int)
    ap.add_argument('--sample', action='store_true')
    ap.add_argument('--output',type=Path, required=True)
    args = ap.parse_args()
    data = run_controls(args.controls) if args.controls else census(args.census,args.limit,args.sample)
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'output':str(args.output),'verdict':data['verdict'],
                      **{k:data[k] for k in ['fixtures_passed','comparisons_passed','mutation_catches'] if k in data}}),flush=True)


if __name__ == '__main__':
    main()
