#!/usr/bin/env python3
"""One-shot fresh review instrument; no project imports or prior checker lineage.
Reads frozen merge fixtures, builds undirected graphs and exact partitions, and
emits per-case acceptance/catch receipts. A mismatch aborts; controls must prove
both rejection and clean-twin acceptance. Not a universal or Python-DP proof.
"""
import argparse
import copy
import hashlib
import json
import pathlib
import time

BASE = pathlib.Path(__file__).resolve().parent
CONTROL = BASE.parent / 'controls.json'


def unique_object(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise ValueError('duplicate object key: ' + key)
        out[key] = value
    return out


def graph(tree):
    adjacency, labels = {}, {}
    def visit(node, address):
        adjacency[address] = set()
        if address:
            parent = address[:-1]
            adjacency[parent].add(address)
            adjacency[address].add(parent)
        if isinstance(node, str):
            labels[address] = node
        else:
            assert isinstance(node, list) and len(node) == 2, 'binary tree syntax'
            visit(node[0], address + '0')
            visit(node[1], address + '1')
    visit(tree, '')
    return adjacency, labels


def connected(adjacency, subset):
    if not subset:
        return False
    reached = {next(iter(subset))}
    frontier = list(reached)
    while frontier:
        v = frontier.pop()
        for w in adjacency[v] & subset - reached:
            reached.add(w)
            frontier.append(w)
    return reached == subset


def faults(family, require_open=True):
    adjacency, labels = graph(family['tree'])
    regions = family['regions']
    errors, seen = [], set()
    for index, raw in regions.items():
        support = set(raw)
        if len(raw) != len(support): errors.append('duplicate support vertex:' + index)
        if not support <= adjacency.keys():
            errors.append('unbounded:' + index)
            continue
        if not connected(adjacency, support): errors.append('disconnected:' + index)
        if not support & labels.keys(): errors.append('leafless:' + index)
        if seen & support: errors.append('overlap:' + index)
        seen |= support
    if not labels.keys() <= seen: errors.append('missing leaf coverage')
    boundary = family['boundary']
    owners = {index for index, support in regions.items() if '' in support}
    if boundary is None:
        if require_open: errors.append('missing designated boundary')
        if owners: errors.append('root owned despite absent boundary')
    elif boundary not in regions or owners != {boundary}:
        errors.append('wrong root boundary ownership')
    return errors


def stats(family):
    return {'blocks': len(family['regions']),
            'cost': len(family['regions']) - int(family['boundary'] is not None)}


def merge(left, right):
    assert not faults(left), faults(left)
    assert not faults(right), faults(right)
    output = {'tree': [left['tree'], right['tree']], 'regions': {'M': ['']}, 'boundary': 'M'}
    for child, direction, prefix in [(left, '0', 'L:'), (right, '1', 'R:')]:
        for index, vertices in child['regions'].items():
            lifted = [direction + vertex for vertex in vertices]
            if index == child['boundary']:
                output['regions']['M'] += lifted
            else:
                output['regions'][prefix + index] = lifted
    return output


def normalized_regions(regions):
    return {index: sorted(vertices) for index, vertices in regions.items()}


def result_faults(output, case):
    errors = faults(output)
    expected = case['expected']
    if normalized_regions(output['regions']) != normalized_regions(expected['regions']):
        errors.append('exact support/index mismatch')
    if output['boundary'] != expected['boundary']: errors.append('exact boundary mismatch')
    for field, value in stats(output).items():
        if value != expected[field]: errors.append(field + ' mismatch')
    _, labels = graph(output['tree'])
    merged_labels = {labels[v] for v in output['regions']['M'] if v in labels}
    if merged_labels != set(expected['merged_labels']): errors.append('merged label membership mismatch')
    for vertex in expected.get('unused_vertices', []):
        if any(vertex in support for support in output['regions'].values()):
            errors.append('unused vertex filled:' + vertex)
    lstat, rstat = stats(case['left']), stats(case['right'])
    if stats(output)['blocks'] != lstat['blocks'] + rstat['blocks'] - 1:
        errors.append('universal block equation')
    if stats(output)['cost'] != lstat['cost'] + rstat['cost']:
        errors.append('universal cost equation')
    return errors


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--pilot', action='store_true')
    parser.add_argument('--false-proposition', action='store_true')
    parser.add_argument('--output', type=pathlib.Path)
    args = parser.parse_args()
    started = time.perf_counter()
    data = json.loads(CONTROL.read_text(), object_pairs_hook=unique_object)
    assert [len(data[k]) for k in ['positive', 'malformed', 'wrong_results', 'support_corruptions']] == [5, 4, 4, 3]
    cases = {case['id']: case for case in data['positive']}
    t1 = merge(cases['T1-singletons']['left'], cases['T1-singletons']['right'])
    assert not faults(t1), 'clean proposition twin must pass'
    if args.false_proposition:
        t1['regions']['M'].remove('')
        assert not faults(t1), 'FALSE PROPOSITION: deleting T1 root preserves a valid open family; actual=' + repr(faults(t1))
        raise RuntimeError('false proposition unexpectedly passed')
    rows = []
    for case in data['positive'][:1] if args.pilot else data['positive']:
        output = merge(case['left'], case['right'])
        assert not result_faults(output, case), (case['id'], result_faults(output, case))
        rows.append({'kind': 'positive', 'id': case['id'], 'actual': output, **stats(output), 'pass': True})
    if not args.pilot:
        for case in data['malformed']:
            errors = faults(case['left']) + faults(case['right'])
            assert errors, case['id']
            rows.append({'kind': 'malformed', 'id': case['id'], 'caught': errors})
        for case in data['wrong_results']:
            fixture = cases[case['fixture']]
            output = merge(fixture['left'], fixture['right'])
            actual = stats(output)[case['field']]
            assert actual != case['wrong'], case['id']
            assert actual == case['clean'], case['id']
            rows.append({'kind': 'wrong_numeric_and_clean', 'id': case['id'], 'actual': actual, 'wrong_rejected': case['wrong'], 'clean_accepted': case['clean']})
        for case in data['support_corruptions']:
            fixture = cases[case['fixture']]
            clean = merge(fixture['left'], fixture['right'])
            assert not result_faults(clean, fixture), case['id']
            bad = copy.deepcopy(clean)
            bad['regions'][case['region']].remove(case['remove'])
            errors = result_faults(bad, fixture)
            assert errors, case['id']
            rows.append({'kind': 'support_corruption_and_clean', 'id': case['id'], 'caught': errors, 'clean_accepted': True})
        repeated = {'id': 'repeated-labels', 'left': {'tree': ['x', 'x'], 'regions': {'o': ['', '0'], 'c': ['1']}, 'boundary': 'o'}, 'right': {'tree': 'x', 'regions': {'o': ['']}, 'boundary': 'o'}, 'expected': {'regions': {'M': ['', '0', '00', '1'], 'L:c': ['01']}, 'boundary': 'M', 'blocks': 2, 'cost': 1, 'merged_labels': ['x']}}
        output = merge(repeated['left'], repeated['right'])
        assert not result_faults(output, repeated), result_faults(output, repeated)
        assert len(graph(output['tree'])[1]) == 3
        rows.append({'kind': 'supplementary', 'id': 'repeated-labels', 'leaf_occurrences': 3, **stats(output), 'pass': True})
        fixture = cases['unused-internal-vertex']
        bad = merge(fixture['left'], fixture['right'])
        bad['regions']['M'].append('01')
        assert not faults(bad), 'extra unused vertex should stay a valid family'
        errors = result_faults(bad, fixture)
        assert 'exact support/index mismatch' in errors
        rows.append({'kind': 'supplementary', 'id': 'extra-valid-internal-vertex', 'caught': errors, 'valid_family': True})
    summary = {'pilot': args.pilot, 'checker_sha256': hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(), 'controls_sha256': hashlib.sha256(CONTROL.read_bytes()).hexdigest(), 'rows': rows, 'elapsed_seconds': time.perf_counter() - started}
    if args.output:
        args.output.write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({'pilot': args.pilot, 'rows': len(rows), 'elapsed_seconds': summary['elapsed_seconds'], 'pass': True}))


if __name__ == '__main__':
    main()
