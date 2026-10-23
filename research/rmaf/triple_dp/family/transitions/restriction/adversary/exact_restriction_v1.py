#!/usr/bin/env python3
"""One-shot independent X0 instrument for the pinned restriction increment.
Fresh address graph, BFS paths, direct predicate restriction and tagged transition
reconstruction. This is a bounded falsifier, not a Lean/executable-refinement proof.
"""
import argparse
import copy
import hashlib
import itertools
import json
from pathlib import Path
import time
from datetime import datetime, timezone

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[6]
SPEC = BASE.parent
EXACT_NUMERIC = True  # MUTATION_SITE: the copy disables numeric comparisons only.


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def utc():
    return datetime.now(timezone.utc).isoformat()


def graph(tree):
    """Each leaf occurrence has its own address, even if all values coincide."""
    adj, leaves = {}, {}
    def visit(node, addr):
        adj[addr] = set()
        if isinstance(node, list):
            if len(node) != 2:
                raise ValueError('binary tree required')
            for side, child in enumerate(node):
                v = addr + str(side)
                visit(child, v)
                adj[addr].add(v)
                adj[v].add(addr)
        else:
            leaves[addr] = node
    visit(tree, '')
    return adj, leaves


def path_between(adj, a, b):
    todo, prev = [a], {a: None}
    for v in todo:
        if v == b:
            route = set()
            while v is not None:
                route.add(v)
                v = prev[v]
            return route
        for w in adj[v]:
            if w not in prev:
                prev[w] = v
                todo.append(w)
    raise ValueError('disconnected input graph')


def family_errors(f):
    adj, leaves = graph(f['tree'])
    ids, regions, boundary = f['indices'], f['regions'], f['boundary']
    errors = []
    if len(ids) != len(set(ids)):
        errors.append('duplicate-index')
    if set(ids) != set(regions):
        errors.append('incomplete-index-enumeration')
    if boundary is not None and boundary not in regions:
        errors.append('boundary-not-index')
    owners = {}
    for i, raw in regions.items():
        supp = set(raw)
        if not supp <= set(adj):
            errors.append('unbounded:' + i)
            continue
        if not supp & set(leaves):
            errors.append('leafless:' + i)
        for a, b in itertools.combinations(supp, 2):
            if not path_between(adj, a, b) <= supp:
                errors.append('nonconvex:' + i)
                break
        for v in supp:
            if v in owners:
                errors.append('overlap:' + v)
            owners[v] = i
        if ('' in supp) != (boundary == i):
            errors.append('root-spec:' + i)
    if not set(leaves) <= set(owners):
        errors.append('uncovered-leaf')
    return errors


def live_sets(f):
    _, leaves = graph(f['tree'])
    return [{i for i in f['indices'] if any(a.startswith(side) and a in leaves
            for a in f['regions'][i])} for side in ('0', '1')]


def premise(f):
    o = f['boundary']
    live = live_sets(f)
    return o is None or all(not any(a.startswith(str(s)) for a in f['regions'][o])
                            or o in live[s] for s in (0, 1))


def charge(f):
    return int(f['boundary'] is not None)


def count(f):
    return len(f['indices'])


def cost(f):
    return count(f) - charge(f)


def restrict(f, side):
    live = live_sets(f)[side]
    ids = [i for i in f['indices'] if i in live]
    regions = {i: sorted(a[1:] for a in f['regions'][i] if a.startswith(str(side)))
               for i in ids}
    root_owners = [i for i in ids if '' in regions[i]]
    if len(root_owners) > 1:
        raise ValueError('restriction has multiple root owners')
    return {'tree': f['tree'][side], 'indices': ids, 'regions': regions,
            'boundary': root_owners[0] if root_owners else None}


def reconstruct(f, left, right, kind):
    """Fresh constructor index tags; explicit map back to original parent ids."""
    regions, mapping = {}, {}
    o = f['boundary']
    for side, child in enumerate((left, right)):
        for n, i in enumerate(child['indices']):
            if kind == 'merge' and i == child['boundary']:
                key = 'M'
            else:
                key = str(side) + ':' + str(n)
            regions.setdefault(key, set()).update(str(side) + a for a in child['regions'][i])
            if key in mapping and mapping[key] != i:
                raise ValueError('joined unequal parent indices')
            mapping[key] = i
    boundary = None
    if kind != 'closeBoth':
        chosen = [key for key, i in mapping.items() if i == o]
        if len(chosen) != 1:
            raise ValueError('parent boundary has nonunique reconstruction')
        boundary = chosen[0]
        regions[boundary].add('')
    return {'tree': f['tree'], 'indices': list(regions),
            'regions': {i: sorted(s) for i, s in regions.items()}, 'boundary': boundary}, mapping


def evaluate(f):
    errors = family_errors(f)
    if errors:
        return {'family_valid': False, 'errors': errors}
    live = live_sets(f)
    in_regime = premise(f)
    result = {'family_valid': True, 'open_branch_live': in_regime,
              'live_left_indices': sorted(live[0]), 'live_right_indices': sorted(live[1])}
    if not in_regime:
        return result
    left, right = restrict(f, 0), restrict(f, 1)
    o = f['boundary']
    kind = ('closeBoth' if o is None else 'merge' if o in live[0] & live[1]
            else 'extendLeft' if o in live[0] else 'extendRight')
    toll = {'closeBoth': charge(left) + charge(right), 'extendLeft': charge(right),
            'extendRight': charge(left), 'merge': 0}[kind]
    reconstructed, mapping = reconstruct(f, left, right, kind)
    occupied = [{i for i in f['indices'] if any(a.startswith(str(s)) for a in f['regions'][i])}
                for s in (0, 1)]
    both = int(o is not None and o in live[0] & live[1])
    props = {
        'left_family_valid': not family_errors(left),
        'right_family_valid': not family_errors(right),
        'occupied_exactly_live': occupied == live,
        'parent_live_somewhere': live[0] | live[1] == set(f['indices']),
        'overlap_exactly_boundary_both': live[0] & live[1] == ({o} if both else set()),
        'count_equation': count(left) + count(right) == count(f) + both,
        'cost_equation': cost(f) == cost(left) + cost(right) + toll,
        'reconstructed_family_valid': not family_errors(reconstructed),
        'bijection_injective': len(set(mapping.values())) == len(mapping),
        'bijection_surjective': set(mapping.values()) == set(f['indices']),
        'recovered_exact_support': all(set(reconstructed['regions'][key]) == set(f['regions'][i])
                                       for key, i in mapping.items()),
        'recovered_exact_boundary': (None if reconstructed['boundary'] is None else
                                     mapping[reconstructed['boundary']]) == o,
        'recovered_count': count(reconstructed) == count(f),
        'recovered_cost': cost(reconstructed) == cost(f),
    }
    for s, child in enumerate((left, right)):
        expected_owner = [i for i in f['indices'] if str(s) in f['regions'][i]]
        props['child_root_owner_' + str(s)] = (child['boundary'] ==
                        (expected_owner[0] if expected_owner else None))
        props['child_enumeration_' + str(s)] = (child['indices'] ==
                        [i for i in f['indices'] if i in live[s]])
        props['child_support_' + str(s)] = all(set(child['regions'][i]) ==
                       {a[1:] for a in f['regions'][i] if a.startswith(str(s))}
                       for i in child['indices'])
    result.update({'kind': kind, 'left_regions': left['regions'], 'right_regions': right['regions'],
       'left_boundary': left['boundary'], 'right_boundary': right['boundary'],
       'parent_count': count(f), 'parent_cost': cost(f), 'left_count': count(left),
       'right_count': count(right), 'left_cost': cost(left), 'right_cost': cost(right),
       'toll': toll, 'properties': props, 'reconstruction': reconstructed, 'index_bijection': mapping})
    return result


def compare(actual, expected, prefix=''):
    errors = []
    for key, value in expected.items():
        name = prefix + key
        if key not in actual:
            errors.append(name + ':missing')
        elif type(value) is int and type(actual[key]) is int:
            if EXACT_NUMERIC and value != actual[key]:
                errors.append(name + ':numeric')
        elif isinstance(value, dict) and isinstance(actual[key], dict):
            if set(value) != set(actual[key]):
                errors.append(name + ':indices')
            errors += compare(actual[key], value, name + '.')
        elif value != actual[key]:
            errors.append(name + ':exact')
    return errors


def verify_pins():
    manifest = json.loads((BASE / 'PRE-RUN-PINS-v1.json').read_text())
    for filename, digest in manifest['sha256'].items():
        if sha(ROOT / filename) != digest:
            raise ValueError('pin drift: ' + filename)
    frozen = json.loads((SPEC / 'PRECONSTRUCTION-SHA256.json').read_text())
    for filename, digest in frozen['sha256'].items():
        if sha(ROOT / filename) != digest:
            raise ValueError('frozen target/control drift: ' + filename)
    return {'manifest_sha256': sha(BASE / 'PRE-RUN-PINS-v1.json'),
            'executed_code_sha256': sha(__file__), 'controls_sha256': sha(SPEC / 'controls.json')}


def controls():
    c = json.loads((SPEC / 'controls.json').read_text())
    expected_sizes = {'positives': 8, 'malformed': 4, 'wrong_numbers': 5,
                      'corruptions': 3, 'outside_premise': 1}
    if {k: len(c[k]) for k in expected_sizes} != expected_sizes:
        raise ValueError('control denominator drift')
    bases = {f['id']: f for f in c['positives']}
    rows = []
    for f in c['positives']:
        actual = evaluate(f)
        errors = compare(actual, f['expected'])
        if not actual.get('family_valid') or not actual.get('open_branch_live'):
            errors.append('input-invalid')
        errors += [p for p, passed in actual.get('properties', {}).items() if not passed]
        rows.append({'id': f['id'], 'type': 'positive', 'pass': not errors,
                     'errors': errors, 'actual': actual})
    for corruption in c['malformed']:
        f = copy.deepcopy(bases[corruption['base']])
        f.update(corruption['replace'])
        actual = evaluate(f)
        rows.append({'id': corruption['id'], 'type': 'malformed',
                     'pass': not actual['family_valid'], 'actual': actual})
    for category in ('wrong_numbers', 'corruptions'):
        for corruption in c[category]:
            f = bases[corruption['base']]
            actual = evaluate(f)
            wrong, clean = copy.deepcopy(f['expected']), copy.deepcopy(f['expected'])
            wrong[corruption['field']] = corruption['wrong']
            clean[corruption['field']] = corruption['correct']
            wrong_errors, clean_errors = compare(actual, wrong), compare(actual, clean)
            rows.append({'id': corruption['id'], 'type': category,
                'pass': bool(wrong_errors) and not clean_errors,
                'wrong_detected': bool(wrong_errors), 'clean_twin_pass': not clean_errors,
                'wrong_errors': wrong_errors, 'clean_errors': clean_errors})
    for f in c['outside_premise']:
        actual = evaluate(f)
        # The raw restriction has a root owner that is not among live indices.
        left = restrict(f, 0)
        expected = {'family_valid': f['expected_family_valid'],
             'open_branch_live': f['expected_open_branch_live'],
             'live_left_indices': f['expected_live_left_indices'],
             'live_right_indices': f['expected_live_right_indices']}
        errors = compare(actual, expected)
        if left['boundary'] == f['forbidden_child_boundary']:
            errors.append('leafless-index-became-child-boundary')
        if f['forbidden_child_boundary'] not in [i for i in f['indices'] if '0' in f['regions'][i]]:
            errors.append('outside-premise-witness-not-present')
        rows.append({'id': f['id'], 'type': 'outside_premise', 'pass': not errors,
                     'errors': errors, 'actual': actual, 'live_only_left': left,
                     'explanation': 'Valid parent; omitted o occupies left root without a left leaf. Premise fails.'})
    failures = [row['id'] for row in rows if not row['pass']]
    return {'stage': 'controls', 'verdict': 'PASS' if not failures else 'FAIL',
            'denominators': expected_sizes, 'rows': rows, 'failures': failures}


def shapes(n):
    if n == 1:
        yield 'x'
    else:
        for k in range(1, n):
            for l in shapes(k):
                for r in shapes(n-k):
                    yield [l, r]


def partitions(items):
    # Restricted-growth labels enumerate every leaf partition exactly once.
    def rec(labels, highest):
        if len(labels) == len(items):
            yield labels
        else:
            for v in range(highest + 2):
                yield from rec(labels + [v], max(v, highest))
    for labels in rec([0], 0):
        yield labels


def candidates(tree):
    adj, leaves = graph(tree)
    leaf_addresses = sorted(leaves)
    internals = sorted(set(adj) - set(leaves))
    for labels in partitions(leaf_addresses):
        k = max(labels) + 1
        ids = ['i' + str(j) for j in range(k)]
        for assignment in itertools.product(range(-1, k), repeat=len(internals)):
            regions = {i: [] for i in ids}
            owners = dict(zip(leaf_addresses, labels))
            owners.update(zip(internals, assignment))
            for a, own in owners.items():
                if own >= 0:
                    regions[ids[own]].append(a)
            yield {'tree': tree, 'indices': ids, 'regions': regions,
                   'boundary': None if owners[''] < 0 else ids[owners['']]}


def hunt(min_leaves, max_leaves, cap_seconds):
    start = time.perf_counter()
    totals = {'candidates': 0, 'valid': 0, 'in_regime': 0, 'outside_premise': 0,
              'closed_parent_child_root': 0, 'unused_internal_vertex': 0,
              'repeated_labels': 0}
    kinds, shape_rows = {}, []
    for n in range(min_leaves, max_leaves + 1):
        for tree in shapes(n):
            t0 = time.perf_counter()
            row = {'tree': tree, 'candidates': 0, 'valid': 0, 'in_regime': 0}
            for f in candidates(tree):
                totals['candidates'] += 1
                row['candidates'] += 1
                out = evaluate(f)
                if out['family_valid']:
                    totals['valid'] += 1
                    row['valid'] += 1
                    if out['open_branch_live']:
                        totals['in_regime'] += 1
                        row['in_regime'] += 1
                        kinds[out['kind']] = kinds.get(out['kind'], 0) + 1
                        totals['repeated_labels'] += 1
                        totals['closed_parent_child_root'] += int(any(
                            i != f['boundary'] and s in f['regions'][i]
                            for s in ('0', '1') for i in f['indices']))
                        adj, _ = graph(tree)
                        totals['unused_internal_vertex'] += int(set(adj) !=
                           set().union(*(set(v) for v in f['regions'].values())))
                        bad = [p for p, passed in out['properties'].items() if not passed]
                        if bad:
                            return {'stage': 'hunt', 'verdict': 'FIRE-CANDIDATE', 'totals': totals,
                                'failing_properties': bad, 'witness': f, 'actual': out,
                                'note': 'Requires independent witness replay before certified FIRE.'}
                    else:
                        totals['outside_premise'] += 1
                if time.perf_counter() - start > cap_seconds:
                    return {'stage': 'hunt', 'verdict': 'TIME-CAP-INCOMPLETE',
                            'totals': totals, 'shape_rows': shape_rows, 'partial_shape': row}
            row['seconds'] = time.perf_counter() - t0
            shape_rows.append(row)
    return {'stage': 'hunt', 'verdict': 'NO-FIRE-BOUNDED', 'totals': totals,
            'transition_counts': kinds, 'shape_rows': shape_rows,
            'range': [min_leaves, max_leaves],
            'scope': 'All leaf partitions/internal ownership assignments on each printed shape; not a universal proof.'}


def main():
    p = argparse.ArgumentParser()
    p.add_argument('stage', choices=['controls', 'hunt'])
    p.add_argument('--out', required=True)
    p.add_argument('--gate')
    p.add_argument('--min-leaves', type=int, default=2)
    p.add_argument('--max-leaves', type=int, default=3)
    p.add_argument('--cap-seconds', type=float, default=15)
    args = p.parse_args()
    started, t0 = utc(), time.perf_counter()
    provenance = verify_pins()
    if args.stage == 'controls':
        result = controls()
    else:
        if not args.gate:
            raise ValueError('control/outer gate receipt required')
        gate = json.loads(Path(args.gate).read_text())
        if gate['verdict'] != 'PASS' or gate['manifest_sha256'] != provenance['manifest_sha256']:
            raise ValueError('control/outer gate failed or different code')
        result = hunt(args.min_leaves, args.max_leaves, args.cap_seconds)
    result.update({'started_utc': started, 'finished_utc': utc(),
                   'elapsed_seconds': time.perf_counter() - t0, **provenance})
    out = Path(args.out)
    with out.open('x') as fh:
        json.dump(result, fh, indent=2, sort_keys=True)
        fh.write('\n')
    summary = {k: v for k, v in result.items() if k in
               ('stage', 'verdict', 'denominators', 'failures', 'totals', 'transition_counts', 'elapsed_seconds')}
    print(json.dumps(summary, sort_keys=True))
    return 0 if result['verdict'] in ('PASS', 'NO-FIRE-BOUNDED') else 1


if __name__ == '__main__':
    raise SystemExit(main())
