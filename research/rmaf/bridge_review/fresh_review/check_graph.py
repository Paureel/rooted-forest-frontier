#!/usr/bin/env python3
"""One-shot independent semantic enumeration for the frozen rMAF graph review.

Use only for CONTROLS.json and complete integer-heap trees. Output is exact
finite Boolean checks, not a universal theorem or rMAF certificate. All frozen
positive/negative controls must match before enumeration. No campaign imports.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parent


def connected(support):
    if not support:
        return False
    # Build raw edges, then expand adjacency closure; do not use ancestor tests.
    edges = [(v // 2, v) for v in support if v != 1 and v // 2 in support]
    reached = {min(support)}
    while True:
        old_size = len(reached)
        for a, b in edges:
            if a in reached:
                reached.add(b)
            if b in reached:
                reached.add(a)
        if len(reached) == old_size:
            return reached == support


def minima(support):
    if not support:
        return []
    depth = min(v.bit_length() - 1 for v in support)
    return sorted(v for v in support if v.bit_length() - 1 == depth)


def region(support, root):
    if root is None or root not in support:
        return False
    for v in support:
        # A root-to-v chain must retain every integer ancestor down to root.
        while v != root:
            if v not in support or v < root:
                return False
            v //= 2
    return True


def controls():
    frozen = json.loads((ROOT / 'CONTROLS.json').read_text())
    rows = []
    for case in frozen['positive'] + frozen['negative']:
        support, root = set(case['support']), case['root']
        ms = minima(support)
        actual = {'connected': connected(support),
                  'region': region(support, root),
                  'minimum_depth_root': root in ms,
                  'unique_minimum': len(ms) == 1}
        for key, value in actual.items():
            if key in case and value != case[key]:
                raise AssertionError((case['name'], key, case[key], value))
        rows.append({'name': case['name'], 'expected_matched': True, **actual})
    # Prove comparator rejects an incorrect claim, then continue normally.
    rejected = []
    for name, actual, false_claim in [
        ('false_connectivity_claim', connected({2, 8}), True),
        ('false_rooted_region_claim', region({1, 2}, 2), True),
        ('false_nonunique_root_claim', len(minima({2, 4, 5})) == 1, False),
    ]:
        try:
            assert actual == false_claim, name
        except AssertionError:
            rejected.append(name)
        else:
            raise AssertionError('Comparator accepted corrupted expectation: ' + name)
    return rows, rejected


def enumerate_tree(height):
    n = 2 ** (height + 1) - 1
    counts = {'vertices': n, 'subsets_checked': 0, 'nonempty_connected': 0,
              'disconnected_nonempty': 0, 'region_checks': 0,
              'nonminimum_root_rejections': 0, 'empty_subsets': 0}
    start = time.perf_counter()
    for mask in range(2 ** n):
        support = {i + 1 for i in range(n) if mask & (1 << i)}
        conn = connected(support)
        ms = minima(support)
        counts['subsets_checked'] += 1
        if not support:
            assert not conn and not ms and not region(support, None)
            counts['empty_subsets'] += 1
            continue
        if conn:
            counts['nonempty_connected'] += 1
            assert len(ms) == 1, ('nonunique minimum', sorted(support), ms)
        else:
            counts['disconnected_nonempty'] += 1
        # Check every proposed root, including all wrong depth choices.
        for root in sorted(support):
            actual_region = region(support, root)
            expected_region = conn and len(ms) == 1 and root == ms[0]
            counts['region_checks'] += 1
            assert actual_region == expected_region, (sorted(support), root)
            if conn and root not in ms:
                assert not actual_region
                counts['nonminimum_root_rejections'] += 1
    assert counts['subsets_checked'] == 2 ** n
    assert counts['empty_subsets'] == 1
    counts['elapsed_seconds'] = time.perf_counter() - start
    return counts


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--height', type=int, choices=[2, 3], required=True)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    cases, rejected = controls()
    census = enumerate_tree(args.height)
    receipt = {'status': 'PASS_FINITE_MODEL_CHECKS', 'height': args.height,
               'controls_sha256': hashlib.sha256((ROOT / 'CONTROLS.json').read_bytes()).hexdigest(),
               'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'controls': cases, 'corrupted_expectations_rejected': rejected,
               'census': census,
               'scope': 'Exact finite integer-heap graph model only; no general algorithm or complexity claim.'}
    (ROOT / args.output).write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
