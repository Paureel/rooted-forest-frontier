#!/usr/bin/env python3
"""One-shot X0 graph-support falsifier. No author family code is imported.

Reach here for the finite FAMILY-TARGET boundary attack, not a DP solver.
Output is exact fixture results and bounded NO-FIRE/FIRE evidence, never proof.
Believe a run only after its frozen positive/corruption controls pass; this
same-author checker still requires fresh independent review for acceptance.
"""
from __future__ import annotations
import argparse
from collections import deque
from datetime import datetime, timezone
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
from time import perf_counter

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
FIXTURES = HERE / 'controls-v1.json'

class Alarm(Exception):
    def __init__(self, code, detail=None):
        self.code, self.detail = code, detail
        super().__init__(code)

def require(ok, code, detail=None):
    if not ok:
        raise Alarm(code, detail)

class Tree:
    def __init__(self, labels):
        self.labels = labels
        self.vertices = {p[:k] for p in labels for k in range(len(p)+1)}
        self.adj = {p: set() for p in self.vertices}
        for p in self.vertices - {''}:
            self.adj[p].add(p[:-1])
            self.adj[p[:-1]].add(p)
        require(len(set(labels.values())) == len(labels), 'repeated_leaf_label')
        for p in self.vertices:
            children = {p+s for s in '01'} & self.vertices
            require(children == set() if p in labels else len(children) == 2,
                    'not_finite_labelled_binary_tree', p)
        self.paths = {}
        for a in self.vertices:
            for b in self.vertices:
                # Explicit graph BFS, independent of binary LCA definitions.
                queue = deque([(a, [a])])
                seen = {a}
                while queue:
                    u, route = queue.popleft()
                    if u == b:
                        self.paths[a, b] = frozenset(route)
                        break
                    for w in sorted(self.adj[u] - seen):
                        seen.add(w)
                        queue.append((w, route+[w]))

    def block(self, support):
        return frozenset(self.labels[v] for v in support if v in self.labels)

    def path_convex(self, support):
        return all(self.paths[a,b] <= support for a in support for b in support)

    def span(self, support, open_region=False):
        terminals = set(support) & self.labels.keys()
        if open_region:
            terminals.add('')
        hull = set(terminals)
        for a,b in combinations(terminals,2):
            hull.update(self.paths[a,b])
        return frozenset(hull)

    def child(self, side):
        return Tree({v[1:]: label for v,label in self.labels.items()
                     if v.startswith(side)})


def encode_family(supports, open_id):
    return {'supports': [sorted(x) for x in supports], 'open': open_id}


def validate(tree, supports, open_id, bad=frozenset()):
    if open_id is not None:
        require(0 <= open_id < len(supports) and '' in supports[open_id],
                'open_root_missing')
    for i,s in enumerate(supports):
        require(bool(s), 'empty_region')
        require(s <= tree.vertices, 'vertex_outside_tree', sorted(s-tree.vertices))
        require(bool(tree.block(s)), 'leafless_charged_region', i)
        require(tree.path_convex(s), 'not_path_convex', i)
        require(('' in s) == (i == open_id), 'wrong_root_classification', i)
        require(not bad or tree.block(s) != bad, 'forbidden_full_bad_triple', i)
    for i,j in combinations(range(len(supports)),2):
        require(not supports[i] & supports[j], 'support_overlap', [i,j])
    covered = [v for s in supports for v in s if v in tree.labels]
    require(len(covered) == len(set(covered)) and set(covered) == set(tree.labels),
            'leaf_coverage')


def trim(tree, supports, open_id):
    return [tree.span(s, i == open_id) for i,s in enumerate(supports)]


def cost(supports, open_id):
    return len(supports) - (open_id is not None)


def audit_transform(tree, old, open_id, new, bad=frozenset()):
    validate(tree, new, open_id, bad)
    require(len(old) == len(new), 'block_count_changed')
    for i,(s,t) in enumerate(zip(old,new)):
        require(t <= s, 'support_grew', i)
        require(tree.block(s) == tree.block(t), 'block_labels_changed', i)
    require(cost(old,open_id) == cost(new,open_id), 'closed_cost_changed')


def restrict(tree, supports, side):
    child = tree.child(side)
    kept, ids, discarded = [], [], []
    for i,s in enumerate(supports):
        local = frozenset(v[1:] for v in s if v.startswith(side))
        if local and child.block(local):
            kept.append(local)
            ids.append(i)
        elif local:
            discarded.append({'parent_id': i, 'support': sorted(local), 'labels': []})
    open_id = next((i for i,s in enumerate(kept) if '' in s), None)
    validate(child, kept, open_id)
    return child, kept, open_id, ids, discarded


def check_restriction_assembly(tree, normal, open_id):
    if '' in tree.labels:
        return {'transition':'leaf', 'child_closed_costs':[], 'closing_charge':0}
    assembled = [set() for _ in normal]
    child_costs, closing_charge, active_sides = [], 0, []
    for side in '01':
        child, raw, child_open, ids, discarded = restrict(tree,normal,side)
        require(not discarded, 'normal_form_leafless_child_fragment', discarded)
        normalized_child = trim(child,raw,child_open)
        audit_transform(child,raw,child_open,normalized_child)
        child_costs.append(cost(normalized_child,child_open))
        if child_open is not None:
            parent_id = ids[child_open]
            if parent_id == open_id:
                active_sides.append(side)
            else:
                closing_charge += 1
        for child_id,s in enumerate(normalized_child):
            assembled[ids[child_id]].update(side+v for v in s)
    if open_id is not None:
        assembled[open_id].add('')
        require(len(active_sides) in (1,2), 'empty_active_parent')
    else:
        require(not active_sides, 'inactive_parent_has_continuation')
    assembled = list(map(frozenset,assembled))
    validate(tree,assembled,open_id)
    # The transition may leave a closed child's open stem until that block
    # is closed. Canonicalize before comparing the existence representatives.
    assembled_normal = trim(tree,assembled,open_id)
    require(assembled_normal == normal, 'assembly_block_identity_changed',
            {'assembled':encode_family(assembled_normal,open_id),
             'expected':encode_family(normal,open_id)})
    require(sum(child_costs)+closing_charge == cost(normal,open_id),
            'closed_cost_changed', {'children':child_costs,'charge':closing_charge,
                                    'parent':cost(normal,open_id)})
    transition = 'unused' if open_id is None else (
        'join' if len(active_sides)==2 else 'extend_'+active_sides[0])
    return {'transition':transition,'child_closed_costs':child_costs,
            'closing_charge':closing_charge,'parent_closed_cost':cost(normal,open_id)}


def lca(a,b):
    k = 0
    while k < min(len(a),len(b)) and a[k] == b[k]:
        k += 1
    return a[:k]


def source_disjoint(tree, target, supports):
    blocks = [target.block(s) for s in supports]
    spans = [tree.span({v for v,label in tree.labels.items() if label in b})
             for b in blocks]
    return all(not spans[i] & spans[j] for i,j in combinations(range(len(spans)),2))


def run_controls(data):
    trees = {name:Tree(labels) for name,labels in data['trees'].items()}
    positive = {}
    output = {'positive':[],'corruption':[]}
    for case in data['positive_controls']:
        tree = trees[case['tree']]
        old = list(map(frozenset,case['supports']))
        oid = case['open']
        bad = frozenset(case.get('bad_color',[]))
        validate(tree,old,oid,bad)
        normal = trim(tree,old,oid)
        audit_transform(tree,old,oid,normal,bad)
        require(normal == list(map(frozenset,case['expected'])), 'fixture_normal_mismatch',case['id'])
        require(len(normal) == case['blocks'], 'fixture_blocks_mismatch',case['id'])
        require(cost(normal,oid) == case['closed_cost'], 'fixture_cost_mismatch',case['id'])
        trace = check_restriction_assembly(tree,normal,oid)
        witness = {**case,'actual':encode_family(normal,oid),'assembly':trace}
        if 'source_tree' in case:
            source = trees[case['source_tree']]
            before = source_disjoint(source,tree,old)
            after = source_disjoint(source,tree,normal)
            require(before and after, 'source_disjointness_failed')
            witness['source_disjoint_before_after'] = [before,after]
        output['positive'].append(witness)
        positive[case['id']] = (tree,old,oid,normal,bad)
    for case in data['corruption_controls']:
        if case['id'] == 'gapped_lca_only':
            tree = trees[case['tree']]
            s = frozenset(case['support'])
            actual_lca = all(lca(a,b) in s for a in s for b in s)
            actual_convex = tree.path_convex(s)
            require(actual_lca == case['expected_lca_closed'] and
                    actual_convex == case['expected_path_convex'],'gapped_control_failed')
            # Matched positive twin restores precisely the missing path vertex.
            twin = s | {case['missing_path_vertex']}
            require(tree.path_convex(twin),'gapped_twin_failed')
            output['corruption'].append({**case,'caught':True,
                'actual_lca_closed':actual_lca,'actual_path_convex':actual_convex,
                'clean_twin':sorted(twin),'clean_twin_path_convex':True})
            continue
        if case['id'] == 'force_open_without_root':
            tree = trees[case['tree']]
            old = list(map(frozenset,case['supports']))
            oid, bad = case['open'], frozenset()
            # Match the same supports to the actual root-containing block.
            validate(tree,old,1)
        else:
            tree,old,oid,normal,bad = positive[case['twin']]
        actual = None
        detail = None
        try:
            if case['id'] == 'charge_empty_child_fragment':
                child,kept,child_open,ids,dropped = restrict(tree,old,case['child'])
                require(dropped == [{'parent_id':0,'support':case['leafless_local_support'],'labels':[]}],
                        'wrong_fragment_fixture',dropped)
                require(len(kept)==case['expected_retained_blocks'] and
                        cost(kept,child_open)==case['expected_closed_cost'],'wrong_child_cost_fixture')
                detail = {'discarded':dropped,'retained':encode_family(kept,child_open),
                          'correct_cost':cost(kept,child_open),'planted_cost':case['mutant_closed_cost']}
                require(case['mutant_closed_cost']==cost(kept,child_open),'closed_cost_changed',detail)
            elif case['id'] == 'force_open_without_root':
                validate(tree,old,oid)
            else:
                mutant = list(map(frozenset,case['mutant_supports']))
                audit_transform(tree,old,oid,mutant,bad)
        except Alarm as exc:
            actual = exc.code
            if detail is None:
                detail = exc.detail
        require(actual==case['expected_alarm'],'corruption_not_caught',{'case':case['id'],'actual':actual})
        output['corruption'].append({**case,'caught':True,'alarm':actual,'detail':detail,'clean_twin_passed':True})
    return trees,output


def probes(trees,names):
    receipt = {'families':0,'supports_considered':0,'per_tree':{},'transition_counts':{},'discarded_raw_fragments':0}
    for name in names:
        tree = trees[name]
        vertices = sorted(tree.vertices)
        count = 0
        for bits in range(1,1<<len(vertices)):
            receipt['supports_considered'] += 1
            s = frozenset(v for i,v in enumerate(vertices) if bits>>i & 1)
            if not tree.block(s) or not tree.path_convex(s):
                continue
            family = [s] + [frozenset({v}) for v in sorted(tree.labels) if v not in s]
            oid = 0 if '' in s else None
            validate(tree,family,oid)
            normal = trim(tree,family,oid)
            try:
                audit_transform(tree,family,oid,normal)
                trace = check_restriction_assembly(tree,normal,oid)
                if '' not in tree.labels:
                    for side in '01':
                        child,raw,child_open,ids,dropped = restrict(tree,family,side)
                        receipt['discarded_raw_fragments'] += len(dropped)
                        # Closed label-bearing block identities survive restriction;
                        # no dropped fragment contributes a charge or boundary state.
                        require(all(child.block(x) for x in raw),'retained_leafless_fragment')
            except Alarm as exc:
                raise Alarm(exc.code,{'tree':name,'family':encode_family(family,oid),
                                      'normal':encode_family(normal,oid),'cause':exc.detail})
            count += 1
            receipt['transition_counts'][trace['transition']] = receipt['transition_counts'].get(trace['transition'],0)+1
        receipt['families'] += count
        receipt['per_tree'][name] = count
    return receipt


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--controls-only',action='store_true')
    parser.add_argument('--output',required=True)
    args=parser.parse_args()
    start=perf_counter()
    raw=FIXTURES.read_bytes()
    declared=(HERE/'controls-v1.sha256').read_text().split()[0]
    require(sha256(raw).hexdigest()==declared,'frozen_controls_changed')
    data=json.loads(raw)
    receipt={'schema':'triple-family-adversary-receipt-v1',
             'started_utc':datetime.now(timezone.utc).isoformat(),
             'controls_sha256':declared,'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
             'exact':True,'mode':'controls-only' if args.controls_only else 'bounded-probes'}
    status=0
    try:
        trees,controls=run_controls(data)
        receipt['controls']=controls
        receipt['positive_passes']=len(controls['positive'])
        receipt['corruptions_caught']=len(controls['corruption'])
        require(receipt['positive_passes']==11 and receipt['corruptions_caught']==6,'wrong_control_denominator')
        if not args.controls_only:
            receipt['probes']=probes(trees,data['extra_probe_contract']['trees'])
        receipt['verdict']='CONTROLS-PASS' if args.controls_only else 'NO-FIRE'
        receipt['scope']='Exact finite graph-support controls and fixed-tree probe families only; no universal proof, no DP correctness, no G1 transfer theorem, no fresh-author verification.'
    except Alarm as exc:
        receipt['verdict']='FIRE'
        receipt['alarm']=exc.code
        receipt['witness']=exc.detail
        status=1
    receipt['elapsed_seconds']=perf_counter()-start
    Path(args.output).write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:receipt[k] for k in ('verdict','positive_passes','corruptions_caught','elapsed_seconds') if k in receipt}))
    if 'probes' in receipt:
        print(json.dumps(receipt['probes'],sort_keys=True))
    if status:
        print(json.dumps({'alarm':receipt['alarm'],'witness':receipt['witness']}))
    return status

if __name__=='__main__':
    raise SystemExit(main())
