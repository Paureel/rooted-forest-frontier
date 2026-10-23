"""One-shot labelled-support controls for the family proof interface.

Uses direct undirected paths, not the Lean convex-hull definition. This is
same-author finite regression evidence; the separate X0/fresh checker is
required before accepting any correspondence claim.
"""
import argparse
import hashlib
import itertools
import json
import pathlib
import time

HERE = pathlib.Path(__file__).resolve().parent
RMAF = HERE.parents[1]


def graph(tree):
    adjacency, leaves = {}, {}
    def visit(t, v):
        adjacency[v] = set()
        if isinstance(t, str):
            leaves[v] = t
        else:
            assert len(t) == 2
            for side, child in enumerate(t):
                w = v + str(side)
                visit(child, w)
                adjacency[v].add(w)
                adjacency[w].add(v)
    visit(tree, '')
    return adjacency, leaves


def path(adj, a, b):
    queue = [(a, [a])]
    seen = {a}
    for v, walk in queue:
        if v == b:
            return set(walk)
        for w in adj[v] - seen:
            seen.add(w)
            queue.append((w, walk + [w]))
    raise AssertionError('disconnected input tree')


def convex(adj, region):
    return region <= adj.keys() and all(path(adj, a, b) <= region
        for a, b in itertools.product(region, repeat=2))


def hull(adj, seeds):
    if not seeds:
        return set()
    return set().union(*(path(adj, a, b)
        for a, b in itertools.product(seeds, repeat=2)))


def valid(adj, leaves, regions, open_index):
    if open_index is not None and not 0 <= open_index < len(regions):
        return False
    return (all(convex(adj, r) and r & leaves.keys() for r in regions)
        and all(not a & b for a, b in itertools.combinations(regions, 2))
        and all(sum(v in r for r in regions) == 1 for v in leaves)
        and all(('' in r) == (i == open_index) for i, r in enumerate(regions)))


def check(row):
    adj, leaves = graph(row['tree'])
    if row['id'] == 'gapped-lca':
        region = set(row['region'])
        def lca(a, b):
            i = 0
            while i < min(len(a), len(b)) and a[i] == b[i]:
                i += 1
            return a[:i]
        lca_closed = all(lca(a, b) in region for a, b in itertools.product(region, repeat=2))
        assert lca_closed == row['lca_closed']
        assert convex(adj, region) == row['path_convex']
        return dict(id=row['id'], lca_closed=lca_closed, path_convex=convex(adj,region))
    regions = list(map(set, row['regions']))
    expected_valid = row.get('family_valid', True)
    actual_valid = valid(adj, leaves, regions, row['open'])
    assert actual_valid == expected_valid
    if not expected_valid:
        return dict(id=row['id'], rejected=True)
    trimmed = [hull(adj, (r & leaves.keys()) | ({''} if i == row['open'] else set()))
               for i, r in enumerate(regions)]
    assert valid(adj, leaves, trimmed, row['open'])
    assert all(t <= r and t & leaves.keys() == r & leaves.keys()
               for t, r in zip(trimmed, regions))
    assert len(trimmed) == len(regions)
    if 'trimmed' in row:
        assert trimmed == list(map(set,row['trimmed']))
        assert len(regions) == row['blocks']
        assert len(regions) - (row['open'] is not None) == row['closed_cost']
    if 'right_fragment' in row:
        fragment = {v for v in regions[row['open']] if v.startswith('1')}
        assert fragment == set(row['right_fragment'])
        assert sorted(leaves[v] for v in fragment & leaves.keys()) == row['right_fragment_labels']
        assert fragment & leaves.keys() == set()
        assert not any(v.startswith('1') for v in trimmed[row['open']])
        assert row['charged_blocks_added'] == 0
    if 'bad_colors' in row:
        merged_labels = {leaves[v] for v in set.union(*regions) & leaves.keys()}
        merged_valid = all(merged_labels != set(color) for color in row['bad_colors'])
        assert merged_valid == row['merged_full_color_valid']
    return dict(id=row['id'], valid=True, trimmed=[sorted(t) for t in trimmed],
                labels_preserved=True, closed_cost=len(regions)-(row['open'] is not None))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--pilot', action='store_true')
    args = parser.parse_args()
    control_path = HERE/'controls.json'
    controls = json.loads(control_path.read_text())
    frozen = json.loads((HERE/'PRECONSTRUCTION-SHA256.json').read_text())
    assert hashlib.sha256(control_path.read_bytes()).hexdigest() == frozen['controls.json']
    rows = controls['known_regressions'] + controls['new_controls']
    if args.pilot:
        rows = rows[:2]
    start = time.perf_counter()
    outcomes = [check(row) for row in rows]
    if not args.pilot:
        for row in controls['malformed_or_corrupt']:
            if 'tree' in row:
                outcomes.append(check(row))
            elif row['id'] == 'drop-open-stem-mutant':
                reference = next(x for x in rows if x['id'] == row['control'])
                adj, _ = graph(reference['tree'])
                assert convex(adj,set(row['mutant_support'])) == row['path_convex']
                assert convex(adj,set(row['clean_twin_support']))
                outcomes.append(dict(id=row['id'], mutant_caught=True, clean_twin=True))
            else:
                assert row['mutant_added_charge'] != row['expected_added_charge']
                outcomes.append(dict(id=row['id'], mutant_caught=True, clean_twin_charge=0))
    receipt = dict(status='passed', pilot=args.pilot, count=len(outcomes),
                   seconds=time.perf_counter()-start, outcomes=outcomes,
                   hashes={name:hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                           for name in ['controls.json','check_controls.py']},
                   scope='Finite same-author controls only; no universal claim.')
    output = RMAF/'results'/('triple-family-controls-pilot.json' if args.pilot
                             else 'triple-family-controls.json')
    assert not output.exists(), 'preserve earlier receipt; choose an explicit replay output'
    output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ['status','pilot','count','seconds']}))


if __name__ == '__main__':
    main()
