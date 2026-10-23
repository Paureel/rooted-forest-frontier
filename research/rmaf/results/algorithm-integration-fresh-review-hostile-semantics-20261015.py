#!/usr/bin/env python3
"""One-shot finite witnesses for overreading a frozen local interface.

Fresh code from the frozen definitions; no author scripts or replay are used.
This source-derived model is not an independent replication of the algorithm.
Run with ./bootloops-python and one JSON output path. All cases are fixed.
"""
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
import json
import sys
import time


@dataclass(frozen=True)
class Group:
    origin: tuple
    labels: tuple
    color: int


@dataclass(frozen=True)
class Node:
    origin: tuple
    left: object
    right: object


def leaf_addresses(tree, prefix=()):
    if isinstance(tree, int):
        return [(prefix, tree)]
    return leaf_addresses(tree[0], prefix + (0,)) + leaf_addresses(tree[1], prefix + (1,))


def path_between(a, b):
    common = 0
    while common < min(len(a), len(b)) and a[common] == b[common]:
        common += 1
    return {a[:i] for i in range(common, len(a) + 1)} | {b[:i] for i in range(common, len(b) + 1)}


def support(tree, block):
    selected = [a for a, x in leaf_addresses(tree) if x in block]
    return set().union(*(path_between(a, b) for a in selected for b in selected))


def checks(tree, blocks):
    labels = [x for _, x in leaf_addresses(tree)]
    flat = [x for b in blocks for x in b]
    partition = all(blocks) and all(flat.count(x) == 1 for x in labels) and all(x in labels for x in flat)
    embeddings = all(not support(tree, a) & support(tree, b) for a, b in combinations(blocks, 2))
    return bool(partition), embeddings


def from_tree(tree, color, prefix=()):
    if isinstance(tree, int):
        return Group(prefix, (tree,), color(tree))
    return Node(prefix, from_tree(tree[0], color, prefix + (0,)), from_tree(tree[1], color, prefix + (1,)))


def groups(tree):
    return [tree] if isinstance(tree, Group) else groups(tree.left) + groups(tree.right)


def origins(tree):
    return [tree.origin] if isinstance(tree, Group) else [tree.origin] + origins(tree.left) + origins(tree.right)


def normalize(tree):
    if isinstance(tree, Group):
        return tree
    left, right = normalize(tree.left), normalize(tree.right)
    if isinstance(left, Group) and isinstance(right, Group) and left.color == right.color:
        return Group(tree.origin, left.labels + right.labels, left.color)
    return Node(tree.origin, left, right)


def erase(tree, chosen):
    if tree.origin == chosen:
        return None
    if isinstance(tree, Group):
        return tree
    left, right = erase(tree.left, chosen), erase(tree.right, chosen)
    if left is None:
        return right
    if right is None:
        return left
    return Node(tree.origin, left, right)


def cherry(tree):
    if isinstance(tree, Group):
        return None
    if isinstance(tree.left, Group) and isinstance(tree.right, Group):
        return tree.left, tree.right
    return cherry(tree.left) or cherry(tree.right)


def choose(tree):
    gs = groups(tree)
    if all(g.color == gs[0].color for g in gs):
        return 'finish', ()
    for group in gs:
        if sum(other.color == group.color for other in gs) == 1:
            return 'one', (group,)
    pair = cherry(tree)
    if pair is None or pair[0].color == pair[1].color:
        return 'refuse', ()
    return 'two', pair


def receipt(outputs=(), refusals=(), visited=0, attempts=0, pruned=0):
    return dict(outputs=list(outputs), refusals=list(refusals), visited=visited, attempts=attempts, pruned=pruned)


def attempt(continuation, tree, detached, cuts, group):
    if not group.origin:
        return receipt(refusals=['root'], attempts=1)
    if group.origin in cuts:
        return receipt(refusals=['duplicate'], attempts=1)
    next_tree = erase(tree, group.origin)
    if next_tree is None:
        return receipt(refusals=['entire'], attempts=1)
    result = continuation(next_tree, [group] + detached, [group.origin] + cuts)
    return dict(result, attempts=result['attempts'] + 1)


def step(continuation, tree, detached, cuts):
    tree = normalize(tree)
    kind, selected = choose(tree)
    if kind == 'finish':
        partition = [list(g.labels) for g in detached] + [[x for g in groups(tree) for x in g.labels]]
        return receipt(outputs=[dict(partition=partition, cuts=cuts)], visited=1)
    if kind == 'refuse':
        return receipt(refusals=['chooser'], visited=1)
    branches = [attempt(continuation, tree, detached, cuts, g) for g in selected]
    return dict(outputs=sum((r['outputs'] for r in branches), []),
                refusals=sum((r['refusals'] for r in branches), []),
                visited=1 + sum(r['visited'] for r in branches),
                attempts=sum(r['attempts'] for r in branches),
                pruned=sum(r['pruned'] for r in branches))


def run(budget, tree, detached=None, cuts=None):
    continuation = (lambda *_: receipt(pruned=1)) if budget == 0 else (lambda t, d, c: run(budget - 1, t, d, c))
    return step(continuation, tree, [] if detached is None else detached, [] if cuts is None else cuts)


def exact(label, actual, expected):
    if actual != expected:
        raise AssertionError(f'{label}: {actual!r} != {expected!r}')


start = time.perf_counter()
plants = []
exact('singleton null', run(0, from_tree(7, lambda x: x))['outputs'], [dict(partition=[[7]], cuts=[])])
plants.append('singleton null recovered')
homogeneous = normalize(from_tree((5, 9), lambda _: 0))
exact('homogeneous payload', homogeneous, Group((), (5, 9), 0))
plants.append('homogeneous payload recovered')
try:
    exact('corrupt expected payload', homogeneous, Group((), (5, 8), 0))
except AssertionError:
    plants.append('altered expected payload rejected')
else:
    raise AssertionError('comparison failed to reject corruption')

witnesses = []
tree, blocks = (0, (1, (2, 3))), [[0, 2], [1, 3]]
exact('W1 guards', checks(tree, blocks), (True, False))
collision = sorted(support(tree, blocks[0]) & support(tree, blocks[1]))
exact('W1 collision', collision, [(1,), (1, 1)])
witnesses.append(dict(id='W1', partitionCheck=True, pairwiseEmbeddings=False, collision=collision))

exact('W2 source checks', checks((5, 9), [[5], [9]]), (True, True))
exact('W2 merged groups', len(groups(homogeneous)), 1)
witnesses.append(dict(id='W2', old_blocks=[[5], [9]], new_groups=[list(g.labels) for g in groups(homogeneous)],
                      old_terminal_addresses=[(0,), (1,)], new_projection_addresses=[(), ()]))

exact('W3 source checks', checks((0, 1), [[0], [1]]), (True, True))
small = from_tree((0, 1), lambda x: x)
kind, selected = choose(normalize(small))
exact('W3 choice', (kind, selected[0].origin), ('one', (0,)))
result = run(0, small)
exact('W3 receipt', result, receipt(visited=1, attempts=1, pruned=1))
witnesses.append(dict(id='W3', budget=0, successful_erase=erase(small, (0,)) is not None, receipt=result))

tree, blocks = (0, (1, (2, (3, 4)))), [[0, 2, 4], [1], [3]]
exact('W4 source checks', checks(tree, blocks), (True, True))
kind, selected = choose(normalize(from_tree(tree, lambda x: x % 2)))
exact('W4 choice', (kind, [g.labels for g in selected]), ('two', [(3,), (4,)]))
singleton = [len(next(b for b in blocks if g.labels[0] in b)) == 1 for g in selected]
exact('W4 singleton alternatives', singleton, [True, False])
witnesses.append(dict(id='W4', tree=tree, blocks=blocks, candidates=[list(g.labels) for g in selected], singleton=singleton))

forged = Node((0, 0), Group((0, 0, 0), (0,), 0), Group((1, 1, 1), (1,), 1))
kind, selected = choose(forged)
os = origins(forged)
local_invariants = len(os) == len(set(os)) and () not in origins(forged.left) + origins(forged.right)
exact('W5 local invariants', local_invariants, True)
exact('W5 choice', kind, 'one')
original_vertices = {()} | {a for a, _ in leaf_addresses((0, 1))}
exact('W5 endpoint validity', selected[0].origin in original_vertices, False)
observed_calls = []
def observe(tree, detached, cuts):
    observed_calls.append(dict(payloads=[list(g.labels) for g in groups(tree)], cuts=cuts))
    return receipt()
attempt(observe, forged, [], [], selected[0])
exact('W5 continuation reached', len(observed_calls), 1)
witnesses.append(dict(id='W5', reachable=False, local_origin_guards=True, chosen_origin=selected[0].origin,
                      chosen_origin_valid_in_named_original=False, continuation_calls=observed_calls))

report = dict(scope='finite semantic witnesses only; no independent replication or global closure',
              plants=plants, witnesses=witnesses, elapsed_seconds=time.perf_counter() - start)
Path(sys.argv[1]).write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, separators=(',', ':')))
