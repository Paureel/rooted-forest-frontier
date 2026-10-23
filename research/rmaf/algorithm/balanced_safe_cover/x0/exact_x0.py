#!/usr/bin/env python3
"""One-shot independent X0 exact finite instrument; no production-oracle imports.
Written from RESEARCH.md mathematical definitions, zero evaluator code reuse.
"""
from __future__ import annotations
import argparse
import copy
from collections import defaultdict
from datetime import datetime, timezone
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
import json
from math import ceil
from pathlib import Path
import platform
import time

BASE = Path(__file__).resolve().parent
WORK = BASE.parents[4]
PIN = BASE.parent / 'FROZEN-CONTROLS.json'


def utc():
    return datetime.now(timezone.utc).isoformat()


def normalized(partition):
    return tuple(sorted(tuple(sorted(b)) for b in partition))


def partition_json(p):
    return [list(b) for b in normalized(p)]


class Tree:
    """Literal graph vertices remain even if rooted restrictions suppress them."""
    def __init__(self, data, labels=None):
        self.data = data
        leaves = []
        def names(x):
            if isinstance(x, str):
                leaves.append(x)
            elif isinstance(x, (list, tuple)) and len(x) == 2:
                names(x[0]); names(x[1])
            elif x is not None:
                raise ValueError('not a rooted binary labelled tree')
        names(data)
        if len(leaves) != len(set(leaves)):
            raise ValueError('repeated leaf')
        self.labels = tuple(sorted(leaves)) if labels is None else tuple(labels)
        if set(leaves) != set(self.labels):
            raise ValueError('label mismatch')
        self.bit = {x: 1 << i for i, x in enumerate(self.labels)}
        self.children, self.parent, self.desc, self.label, self.path = {}, {}, {}, {}, {}
        self.edges = []
        def make(x, path):
            v = len(self.path)
            self.path[v] = path
            if isinstance(x, str):
                self.children[v] = ()
                self.label[v] = x
                self.desc[v] = self.bit[x]
            else:
                kids = (make(x[0], path + '0'), make(x[1], path + '1'))
                self.children[v] = kids
                self.desc[v] = self.desc[kids[0]] | self.desc[kids[1]]
                for c in kids:
                    self.parent[c] = v
                    self.edges.append((v, c))
            return v
        self.root = None if data is None else make(data, 'R')
        self.edges.sort(key=lambda e: self.path[e[1]])
        self.adj = {v: set() for v in self.path}
        for a, b in self.edges:
            self.adj[a].add(b); self.adj[b].add(a)
        self.full = (1 << len(self.labels)) - 1

    def mask(self, labels):
        m = 0
        for label in labels:
            m |= self.bit[label]
        return m

    def block(self, mask):
        return tuple(x for x in self.labels if self.bit[x] & mask)

    @lru_cache(None)
    def topology(self, mask):
        if not mask:
            return None
        def prune(v):
            if not (self.desc[v] & mask):
                return None
            if not self.children[v]:
                return ('L', self.label[v])
            kept = [prune(c) for c in self.children[v]]
            kept = [x for x in kept if x is not None]
            if len(kept) == 1:
                return kept[0]
            return ('B',) + tuple(sorted(kept, key=repr))
        return prune(self.root)

    @lru_cache(None)
    def support(self, mask):
        if not mask:
            return frozenset()
        v = self.root
        while self.children[v]:
            containing = [c for c in self.children[v] if (self.desc[c] & mask) == mask]
            if not containing:
                break
            v = containing[0]
        visited = set()
        def walk(w):
            if self.desc[w] & mask:
                visited.add(w)
                for c in self.children[w]:
                    walk(c)
        walk(v)
        return frozenset(visited)

    def support_paths(self, mask):
        return sorted(self.path[v] for v in self.support(mask))

    def cut_partition(self, cut_edges):
        """Independent literal connectivity route, rejects empty/redundant cuts."""
        deleted = set(cut_edges)
        remaining = set(self.path)
        components = []
        while remaining:
            start = min(remaining)
            stack, vertices = [start], set()
            while stack:
                v = stack.pop()
                if v in vertices:
                    continue
                vertices.add(v)
                for w in self.adj[v]:
                    edge = (v, w) if self.parent.get(w) == v else (w, v)
                    if edge not in deleted:
                        stack.append(w)
            remaining -= vertices
            mask = 0
            for v in vertices:
                if v in self.label:
                    mask |= self.bit[self.label[v]]
            if not mask:
                return None
            components.append(mask)
        if len(components) != len(cut_edges) + 1:
            raise AssertionError('literal forest component/cut inconsistency')
        return tuple(sorted(components))

    def precuts(self, blocks):
        """Every distinct minimum source-edge realization of a leaf partition."""
        want = tuple(sorted(blocks))
        if self.root is None:
            return [()] if want == () else []
        count = len(want) - 1
        if count < 0:
            return []
        return [cs for cs in combinations(self.edges, count) if self.cut_partition(cs) == want]

    def edge_json(self, edge):
        a, b = edge
        return {'parent_vertex': self.path[a], 'child_vertex': self.path[b],
                'child_descendant_labels': list(self.block(self.desc[b]))}


@lru_cache(None)
def partitions(mask):
    """Enumerate each set partition once by adjoining the last bit."""
    if mask == 0:
        return ((),)
    bit = mask & -mask
    ans = []
    for p in partitions(mask ^ bit):
        ans.append(tuple(sorted((bit,) + p)))
        for i in range(len(p)):
            ans.append(tuple(sorted(p[:i] + (p[i] | bit,) + p[i + 1:])))
    if len(ans) != len(set(ans)):
        raise AssertionError('duplicate partitions')
    return tuple(ans)


def valid_partition(s, t, p):
    seen_s, seen_t = set(), set()
    for b in p:
        if s.topology(b) != t.topology(b):
            return False
        ss, ts = s.support(b), t.support(b)
        if seen_s.intersection(ss) or seen_t.intersection(ts):
            return False
        seen_s.update(ss); seen_t.update(ts)
    return True


def refines(p, blocks):
    return all(any((b & c) == b for c in blocks) for b in p)


def exact(s, t):
    if s.full != t.full or s.labels != t.labels:
        raise ValueError('different label sets')
    accepted = [p for p in partitions(s.full) if valid_partition(s, t, p)]
    k = min(map(len, accepted))
    optimum = [p for p in accepted if len(p) == k]
    return {'cuts': max(0, k - 1), 'optimum': optimum, 'accepted': accepted,
            'partitions_enumerated': len(partitions(s.full))}


def local_distance(s, t, mask):
    good = [p for p in partitions(mask) if valid_partition(s, t, p)]
    return min(map(len, good)) - 1


def terminals(s, t, blocks):
    triple = all(s.topology(b) == t.topology(b) or b.bit_count() == 3 for b in blocks)
    overlaps = []
    pure = True
    for a, b in combinations(blocks, 2):
        sa, sb = t.support(a), t.support(b)
        meet = sa & sb
        rows = []
        for v in sorted(meet):
            da = len(t.adj[v] & sa)
            db = len(t.adj[v] & sb)
            rows.append({'vertex': t.path[v], 'degree_A': da, 'degree_B': db})
            pure &= (da == 2 and db == 2)
        if rows:
            overlaps.append({'A': list(s.block(a)), 'B': list(s.block(b)), 'vertices': rows})
    return {'pure-bridge': pure, 'compatible-or-triple': triple, 'overlaps': overlaps}


def analyze(source, target, precut_blocks=None):
    s = Tree(source)
    t = Tree(target, s.labels)
    ex = exact(s, t)
    out = {'optimum_cuts': ex['cuts'], 'optimum_partitions': [partition_json([s.block(b) for b in p]) for p in ex['optimum']],
           'optimum_partition_count': len(ex['optimum']), 'partitions_enumerated': ex['partitions_enumerated']}
    if precut_blocks is None:
        precut_blocks = [list(s.labels)] if s.labels else []
    blocks = tuple(sorted(s.mask(b) for b in precut_blocks))
    if not all(blocks) or sum(blocks) != s.full or len(set(blocks)) != len(blocks):
        if s.full or blocks:
            raise ValueError('not a partition')
    realizations = s.precuts(blocks)
    if not realizations:
        raise ValueError('precut blocks not realized by distinct nonredundant source edges')
    refining = [p for p in ex['accepted'] if refines(p, blocks)]
    survive = [p for p in ex['optimum'] if refines(p, blocks)]
    completion = min(map(len, refining)) - len(blocks)
    local = [{'block': list(s.block(b)), 'distance': local_distance(s, t, b)} for b in blocks]
    terminal = terminals(s, t, blocks)
    out.update({'precut_blocks': partition_json([s.block(b) for b in blocks]),
                'precuts': max(0, len(blocks)-1), 'distinct_precut_realization_count': len(realizations),
                'precut_realizations': [[s.edge_json(e) for e in cs] for cs in realizations],
                'surviving_optimum_count': len(survive),
                'surviving_optimum_partitions': [partition_json([s.block(b) for b in p]) for p in survive],
                'one_optimum_survival': bool(survive), 'all_optimum_survival': len(survive) == len(ex['optimum']),
                'completion_cuts': completion, 'charged_total': max(0,len(blocks)-1)+completion,
                'local_distances': local, 'tau': max([r['distance'] for r in local], default=0),
                'terminal_membership': {k:v for k,v in terminal.items() if k != 'overlaps'},
                'actual_target_overlap_geometry': terminal['overlaps']})
    return out


def fixture_actual(f):
    if f['id'] == 'false-exponent':
        an, ad = f['alpha_numerator'], f['alpha_denominator']
        cn, cd = f['local_base_numerator'], f['local_base_denominator']
        tn, td = f['theta_numerator'], f['theta_denominator']
        if (tn, td) != (1,2):
            raise ValueError('this rational certificate pins theta=1/2')
        raw_n, raw_d = an*an*cn, ad*ad*cd
        sq = Fraction(raw_n, raw_d)
        return {'squared_composed_base_numerator':raw_n, 'squared_composed_base_denominator':raw_d,
                'squared_composed_base_reduced': [sq.numerator, sq.denominator],
                'less_than_23391_over_10000': sq < Fraction(23391,10000)**2,
                'false_less_than_19_over_10': sq < Fraction(19,10)**2}
    a = analyze(f['source'], f['target'], f.get('precut_blocks'))
    if 'budget' in f:
        a['half_budget'] = 2*a['tau'] <= f['budget']
    if 'false_unsplit_partition' in f:
        s,t = Tree(f['source']), Tree(f['target'])
        a['false_unsplit_accepted'] = valid_partition(s,t,tuple(s.mask(b) for b in f['false_unsplit_partition']))
    return a


def compare_fixture(f, a):
    mismatches, checks = [], []
    for key, want in f.items():
        if not key.startswith('expected_'):
            continue
        field = key[len('expected_'):]
        if field == 'terminal':
            got = a['terminal_membership'].get(want)
            desired = True
        elif field == 'optimum_partitions':
            got = sorted(normalized(p) for p in a[field]); desired = sorted(normalized(p) for p in want)
        else:
            got, desired = a.get(field), want
        passed = got == desired
        checks.append({'field':field, 'expected':desired, 'actual':got, 'passed':passed})
        if not passed:
            mismatches.append(checks[-1])
    negatives = []
    if 'false_unsplit_partition' in f:
        negatives.append({'detector':'wrong-topology', 'rejected': a['false_unsplit_accepted'] is False})
    if 'false_residual_as_total' in f:
        negatives.append({'detector':'omitted-precut-charge', 'rejected': a['charged_total'] != f['false_residual_as_total']})
    if f.get('expected_one_optimum_survival') is False:
        negatives.append({'detector':'omitted-original-optimum', 'rejected': a['one_optimum_survival'] is False})
    if f.get('expected_all_optimum_survival') is False:
        negatives.append({'detector':'false-all-optima-survive', 'rejected': a['all_optimum_survival'] is False})
    if f.get('expected_half_budget') is False:
        negatives.append({'detector':'failed-tau-halfbudget', 'rejected': a['half_budget'] is False})
    if f['id'] == 'false-exponent':
        negatives.append({'detector':'false-composed-base-below-1.9', 'rejected': a['false_less_than_19_over_10'] is False})
    if not all(x['rejected'] for x in negatives):
        mismatches.extend(negatives)
    return checks, negatives, mismatches


def controls(outpath):
    frozen_bytes = PIN.read_bytes()
    frozen = json.loads(frozen_bytes)
    started = time.perf_counter()
    receipt = {'kind':'independent-X0-frozen-control-audit','started_utc':utc(), 'pin_sha256':sha256(frozen_bytes).hexdigest(),
               'script_sha256':sha256(Path(__file__).read_bytes()).hexdigest(), 'python':platform.python_version(),
               'model':'ordinary rooted unordered binary labelled; no rho; unsuppressed supports; exact integer/fraction',
               'lineage':'fresh code from spec; standard library only; no production evaluator reads/imports',
               'rows':[], 'mismatches':[]}
    for f in frozen['fixtures']:
        st = time.perf_counter()
        actual = fixture_actual(f)
        checks, negatives, bad = compare_fixture(f,actual)
        mutation_receipts = []
        for key, want in f.items():
            if not key.startswith('expected_'):
                continue
            corrupt = copy.deepcopy(f)
            if isinstance(want, bool):
                corrupt[key] = not want
            elif isinstance(want, int):
                corrupt[key] = want + 1
            elif isinstance(want, str):
                corrupt[key] = 'deliberately-nonexistent-terminal'
            else:
                corrupt[key] = [[['deliberately-nonexistent-label']]]
            _, _, mutation_bad = compare_fixture(corrupt, actual)
            caught = bool(mutation_bad)
            mutation_receipts.append({'field':key, 'corrupted_expected':corrupt[key], 'caught':caught})
            if not caught:
                raise AssertionError('full comparator mutation survived: ' + key)
        row = {'id':f['id'], 'seconds':time.perf_counter()-st, 'actual':actual,
               'literal_checks':checks, 'negative_controls':negatives,
               'full_comparator_mutations':mutation_receipts,
               'verdict':'PIN-MISMATCH' if bad else 'REPRODUCES'}
        receipt['rows'].append(row)
        receipt['mismatches'].extend({'id':f['id'], 'detail':b} for b in bad)
        receipt['finished_rows']=len(receipt['rows'])
        outpath.write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps({'id':f['id'],'seconds':row['seconds'],'verdict':row['verdict'],'mismatches':bad}),flush=True)
    receipt['seconds'] = time.perf_counter()-started
    receipt['expected_fixture_count'] = len(frozen['fixtures'])
    receipt['verdict'] = 'PIN-MISMATCH' if receipt['mismatches'] else 'REPRODUCES-ALL-FROZEN-CONTROLS'
    receipt['finished_utc']=utc()
    outpath.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'verdict':receipt['verdict'],'fixtures':len(receipt['rows']),'seconds':receipt['seconds']}),flush=True)
    return not receipt['mismatches']


@lru_cache(None)
def all_trees(labels):
    if len(labels) == 1:
        return (labels[0],)
    first, rest = labels[0], labels[1:]
    ans = []
    for r in range(len(rest)):
        for subset in combinations(rest,r):
            left = tuple(sorted((first,) + subset))
            right = tuple(x for x in labels if x not in left)
            for a in all_trees(left):
                for b in all_trees(right):
                    ans.append((a,b))
    return tuple(ans)


def search(max_n, outpath, pair_limit=None, equal_halves=False, require_halfbudget=False):
    started = time.perf_counter()
    receipt = {'kind':'exact-counterexample-search','started_utc':utc(), 'script_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
               'balancing_definition':'one source-edge cut; both sides nonempty; maximum leaf count <= ceil(2n/3)',
               'claim':'every budget-admissible globally leaf-balanced source-edge split preserves some original optimum',
               'qualification':'finite candidate failure does not refute the safe-cover existence target',
               'additional_restrictions':{'equal_halves':equal_halves,'require_local_halfbudget':require_halfbudget},
               'sizes':[], 'witness':None, 'verdict':'IN-PROGRESS'}
    tested_pairs = 0
    for n in range(1,max_n+1):
        trees = all_trees(tuple(chr(97+i) for i in range(n)))
        size_st = time.perf_counter()
        size = {'n':n,'tree_count':len(trees),'total_ordered_tree_pairs':len(trees)**2,
                'finished_pairs':0,'checked_balanced_splits':0,'checked_halfbudget_balanced_splits':0,'pair_seconds':[]}
        receipt['sizes'].append(size)
        for sd in trees:
            s = Tree(sd)
            balanced = []
            for edge in s.edges:
                p = s.cut_partition((edge,))
                if p and max(x.bit_count() for x in p) <= ceil(2*n/3) and (not equal_halves or len({x.bit_count() for x in p}) == 1):
                    balanced.append((edge,p))
            for td in trees:
                pair_st = time.perf_counter()
                t = Tree(td,s.labels)
                ex = exact(s,t)
                if ex['cuts'] >= 1:
                    for edge,blocks in balanced:
                        size['checked_balanced_splits'] += 1
                        surviving = [p for p in ex['optimum'] if refines(p,blocks)]
                        tau = max(local_distance(s,t,b) for b in blocks)
                        half = 2*tau <= ex['cuts']
                        size['checked_halfbudget_balanced_splits'] += int(half)
                        if require_halfbudget and not half:
                            continue
                        if not surviving:
                            a = analyze(sd,td,[s.block(b) for b in blocks])
                            receipt['witness'] = {'n':n,'source':sd,'target':td,'original_budget':ex['cuts'],
                                'source_cut':s.edge_json(edge), 'split_leaf_sizes':sorted(b.bit_count() for b in blocks),
                                'centroid_balanced':True,'equal_halves':len({b.bit_count() for b in blocks})==1,
                                'local_halfbudget':half,'exact':a}
                            size['finished_pairs'] += 1
                            size['pair_seconds'].append(time.perf_counter()-pair_st)
                            size['seconds']=time.perf_counter()-size_st
                            receipt['seconds']=time.perf_counter()-started
                            receipt['verdict']='CERTIFIED-CANDIDATE-FAILURE'
                            receipt['finished_utc']=utc()
                            outpath.write_text(json.dumps(receipt,indent=2)+'\n')
                            print(json.dumps({'verdict':receipt['verdict'],'n':n,'source':sd,'target':td,
                                'b':ex['cuts'],'tau':tau,'local_halfbudget':half,'seconds':receipt['seconds']}),flush=True)
                            return receipt
                size['finished_pairs'] += 1
                tested_pairs += 1
                size['pair_seconds'].append(time.perf_counter()-pair_st)
                if pair_limit and tested_pairs >= pair_limit:
                    size['seconds']=time.perf_counter()-size_st
                    receipt['seconds']=time.perf_counter()-started
                    receipt['verdict']='PILOT-BOUNDED-NO-FIRE'
                    outpath.write_text(json.dumps(receipt,indent=2)+'\n')
                    print(json.dumps({'verdict':receipt['verdict'],'pairs':tested_pairs,'seconds':receipt['seconds']}),flush=True)
                    return receipt
                if size['finished_pairs'] % 25 == 0:
                    outpath.write_text(json.dumps(receipt,indent=2)+'\n')
        size['seconds']=time.perf_counter()-size_st
        outpath.write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps({'n':n,'pairs':size['finished_pairs'],'balanced_splits':size['checked_balanced_splits'],'seconds':size['seconds']}),flush=True)
    receipt['seconds']=time.perf_counter()-started
    receipt['verdict']='FINITE-NO-FIRE'
    receipt['finished_utc']=utc()
    outpath.write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt


def main():
    p=argparse.ArgumentParser()
    p.add_argument('mode',choices=['controls','search'])
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--max-n',type=int,default=4)
    p.add_argument('--pair-limit',type=int)
    p.add_argument('--equal-halves',action='store_true')
    p.add_argument('--require-halfbudget',action='store_true')
    a=p.parse_args()
    if a.mode=='controls':
        raise SystemExit(0 if controls(a.out) else 1)
    search(a.max_n,a.out,a.pair_limit,a.equal_halves,a.require_halfbudget)

if __name__=='__main__':
    main()
