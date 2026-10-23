#!/usr/bin/env python3
"""One-shot independent rMAF prefix-route checker, 2026-10-14.

What: enumerate selected leaf occurrences, compute their longest common prefix,
and take prefix intervals. Generate Lean exact-membership controls against the
unchanged imported executable; never transliterate rootedSpan/minimalVertices.
When: this independent bridge review only, not a production rMAF solver.
Output: JSON exact addresses/counts/timings and Lean source. Bit 0=left, 1=right.
Acceptance: all nine frozen controls and four corruptions; finite actual-source
comparisons count only after the generated Lean file compiles with `decide`.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent


def selected_occurrences(tree, labels):
    # Iterative address enumeration; no subtree-span recurrence is used.
    todo = [((), tree)]
    out = []
    while todo:
        address, subtree = todo.pop()
        if isinstance(subtree, int):
            if subtree in labels:
                out.append(address)
        else:
            left, right = subtree
            todo.append((address + (1,), right))
            todo.append((address + (0,), left))
    return out


def prefix_hull(tree, labels):
    ends = selected_occurrences(tree, labels)
    if not ends:
        return set()
    bound = min(map(len, ends))
    lca_length = 0
    while lca_length < bound and len({p[lca_length] for p in ends}) == 1:
        lca_length += 1
    return {p[:j] for p in ends for j in range(lca_length, len(p) + 1)}


def tree_graph(tree):
    # Build actual parent-child edges from traversal, separately from hull code.
    vertices, edges = set(), set()
    todo = [((), tree)]
    while todo:
        address, subtree = todo.pop()
        vertices.add(address)
        if not isinstance(subtree, int):
            for bit, child in enumerate(subtree):
                child_address = address + (bit,)
                edges.add((address, child_address))
                todo.append((child_address, child))
    return vertices, edges


def connected(tree, vertices):
    ambient, edges = tree_graph(tree)
    if not vertices or not vertices <= ambient:
        return False
    first = next(iter(vertices))
    reached, todo = {first}, [first]
    while todo:
        current = todo.pop()
        for parent, child in edges:
            neighbor = child if current == parent else parent if current == child else None
            if neighbor is not None and neighbor in vertices and neighbor not in reached:
                reached.add(neighbor)
                todo.append(neighbor)
    return reached == vertices


def addr(word):
    return tuple(map(int, word))


def addresses(*words):
    return {addr(w) for w in words}


BASE = ((0, 1), (2, 3))
DUPLICATE = ((7, 1), (2, 7))
LONG = (8, (8, (8, BASE)))
CASES = [
    ('cross', BASE, (0, 2), addresses('', '0', '00', '1', '10')),
    ('singleton', BASE, (1,), addresses('01')),
    ('left_pair', BASE, (0, 1), addresses('0', '00', '01')),
    ('empty_selection', BASE, (), set()),
    ('absent_label', BASE, (9,), set()),
    ('duplicate_label', DUPLICATE, (7,), addresses('', '0', '00', '1', '11')),
    ('mixed_absent', DUPLICATE, (1, 9), addresses('01')),
    ('long_left_pair', LONG, (0, 1), addresses('1110', '11100', '11101')),
    ('long_cross', LONG, (0, 2), addresses('111', '1110', '11100', '1111', '11110')),
]
CORRUPTIONS = [
    ('missing_path', 0, addresses('', '00', '1', '10')),
    ('wrong_absent_label', 4, addresses('')),
    ('one_duplicate_only', 5, addresses('00')),
    ('unsuppressed_initial_path', 8, addresses('', '1', '11', '111', '1110', '11100', '1111', '11110')),
]


def word(p):
    return ''.join(map(str, p)) or 'epsilon'


def lean_tree(tree):
    if isinstance(tree, int):
        return f'(.leaf {tree})'
    return f'(.node {lean_tree(tree[0])} {lean_tree(tree[1])})'


def lean_labels(labels):
    return '[' + ', '.join(map(str, labels)) + ']'


def lean_vertices(vertices):
    return '[' + ', '.join('[' + ', '.join('true' if b else 'false' for b in p) + ']' for p in sorted(vertices)) + ']'


def trees(leaves):
    if leaves == 1:
        yield 0
        yield 1
        return
    for left_count in range(1, leaves):
        for left in trees(left_count):
            for right in trees(leaves - left_count):
                yield left, right


def control_checks():
    records = []
    for name, tree, labels, expected in CASES:
        observed = prefix_hull(tree, labels)
        assert observed == expected, (name, observed, expected)
        if expected:
            assert connected(tree, observed), name
        records.append({'name': name, 'support': sorted(map(word, observed)), 'vertices': len(observed), 'reproduced': True})
    negatives = []
    for name, case_index, damaged in CORRUPTIONS:
        _, tree, labels, expected = CASES[case_index]
        actual = prefix_hull(tree, labels)
        assert actual == expected
        assert actual != damaged, name
        check_connected = connected(tree, damaged)
        if name == 'missing_path':
            assert not check_connected
        negatives.append({'name': name, 'missing': sorted(map(word, actual - damaged)), 'unexpected': sorted(map(word, damaged - actual)), 'exact_membership_rejected': True, 'damaged_support_connected': check_connected})
    return records, negatives


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-leaves', type=int, choices=range(1, 6), default=3)
    args = parser.parse_args()
    start = time.perf_counter()
    records, negatives = control_checks()  # before enumeration
    generated = ['import RMAF', '', 'namespace PrefixRouteFinite', 'open RMAF',
                 'def sameMembers (xs ys : List Vertex) : Bool :=',
                 '  xs.all (fun x => ys.contains x) && ys.all (fun y => xs.contains y)', '']
    for name, tree, labels, expected in CASES:
        generated.append(f'theorem control_{name} : sameMembers (minimalVertices {lean_labels(labels)} {lean_tree(tree)}) {lean_vertices(expected)} = true := by decide')
    for name, case_index, damaged in CORRUPTIONS:
        _, tree, labels, _ = CASES[case_index]
        generated.append(f'theorem reject_{name} : sameMembers (minimalVertices {lean_labels(labels)} {lean_tree(tree)}) {lean_vertices(damaged)} = false := by decide')
    generated.extend(['', 'set_option maxRecDepth 65536', 'set_option maxHeartbeats 4000000', ''])
    sweep_count, tree_count, layer_data = 0, 0, []
    for leaf_count in range(1, args.max_leaves + 1):
        layer_start, before_trees, before_cases = time.perf_counter(), tree_count, sweep_count
        for tree in trees(leaf_count):
            tree_count += 1
            for bits in itertools.product((False, True), repeat=3):
                labels = tuple(x for x, present in zip((0, 1, 9), bits) if present)
                hull = prefix_hull(tree, labels)
                if hull:
                    assert connected(tree, hull)
                else:
                    assert not selected_occurrences(tree, labels)
                generated.append(f'theorem sweep_{sweep_count:04} : sameMembers (minimalVertices {lean_labels(labels)} {lean_tree(tree)}) {lean_vertices(hull)} = true := by decide')
                sweep_count += 1
        layer_data.append({'leaves': leaf_count, 'trees': tree_count - before_trees, 'cases': sweep_count - before_cases, 'seconds': time.perf_counter() - layer_start})
    generated.append('')
    for name, *_ in CASES:
        generated.append(f'#print axioms control_{name}')
    for name, *_ in CORRUPTIONS:
        generated.append(f'#print axioms reject_{name}')
    generated.extend(['#print axioms sweep_0000', f'#print axioms sweep_{sweep_count-1:04}', 'end PrefixRouteFinite', ''])
    output = HERE / f'Finite{args.max_leaves}.lean'
    output.write_text('\n'.join(generated))
    controls_hash = hashlib.sha256((HERE / 'CONTROLS.md').read_bytes()).hexdigest()
    summary = {'controls_frozen_sha256': controls_hash, 'exact_control_count': len(records), 'negative_control_count': len(negatives), 'controls': records, 'corruptions': negatives, 'sweep_tree_count': tree_count, 'sweep_comparison_count': sweep_count, 'layers': layer_data, 'generation_seconds': time.perf_counter() - start, 'lean_source': output.name, 'lean_status': 'NOT YET RUN: this JSON records Python checks only'}
    (HERE / f'python-{args.max_leaves}.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: summary[k] for k in ('exact_control_count','negative_control_count','sweep_tree_count','sweep_comparison_count','generation_seconds','lean_source','lean_status')}))


if __name__ == '__main__':
    main()
