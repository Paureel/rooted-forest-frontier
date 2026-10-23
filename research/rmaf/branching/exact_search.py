#!/usr/bin/env python3
"""Problem-specific exact rMAF counterexample instrument, independently written.

Representation: unordered rooted binary trees as canonical nested tuples of
integer leaves. Agreement is equality of restricted rooted trees; embeddings
are sets of vertex-addresses in each original tree and must be disjoint.
This checks finite instances only and is not an FPT algorithm or a proof.
"""
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import argparse
import json
import time


def node(a, b):
    return tuple(sorted((a, b), key=repr))


@lru_cache(None)
def trees(labels):
    if len(labels) == 1:
        return (labels[0],)
    root = labels[0]
    output = []
    rest = labels[1:]
    for size in range(len(rest)):
        for choice in combinations(rest, size):
            left = (root,) + choice
            right = tuple(x for x in rest if x not in choice)
            for a in trees(left):
                for b in trees(right):
                    output.append(node(a, b))
    return tuple(output)


def restrict(tree, labels):
    if isinstance(tree, int):
        return tree if tree in labels else None
    a, b = (restrict(child, labels) for child in tree)
    if a is None:
        return b
    if b is None:
        return a
    return node(a, b)


def leaves(tree):
    if isinstance(tree, int):
        return frozenset((tree,))
    return leaves(tree[0]) | leaves(tree[1])


@lru_cache(None)
def paths(tree):
    result = {}
    def walk(t, p):
        if isinstance(t, int):
            result[t] = p
        else:
            walk(t[0], p + (0,))
            walk(t[1], p + (1,))
    walk(tree, ())
    return result


def embedding(tree, block):
    ps = [paths(tree)[x] for x in block]
    prefix = 0
    while all(len(p) > prefix and p[prefix] == ps[0][prefix] for p in ps):
        prefix += 1
    return frozenset(p[:i] for p in ps for i in range(prefix, len(p) + 1))


def valid(tree, other, partition):
    blocks = tuple(frozenset(block) for block in partition)
    if any(not block for block in blocks):
        return False
    if frozenset().union(*blocks) != leaves(tree) or leaves(tree) != leaves(other):
        return False
    if sum(map(len, blocks)) != len(leaves(tree)):
        return False
    if any(restrict(tree, b) != restrict(other, b) for b in blocks):
        return False
    for t in (tree, other):
        used = set()
        for block in blocks:
            vertices = embedding(t, block)
            if used & vertices:
                return False
            used.update(vertices)
    return True


def partitions(labels):
    if not labels:
        yield ()
        return
    x, *tail = labels
    for parts in partitions(tail):
        yield ((x,),) + parts
        for i in range(len(parts)):
            yield parts[:i] + ((x,) + parts[i],) + parts[i + 1:]


@lru_cache(None)
def all_partitions(labels):
    return tuple(sorted(partitions(labels), key=len))


def optimum(tree, other):
    accepted = []
    best = len(leaves(tree))
    for partition in all_partitions(tuple(sorted(leaves(tree)))):
        if len(partition) > best:
            break
        if valid(tree, other, partition):
            best = len(partition)
            accepted.append(partition)
    return best, accepted


def cherries(tree):
    if isinstance(tree, int):
        return []
    if all(isinstance(child, int) for child in tree):
        return [tree]
    return cherries(tree[0]) + cherries(tree[1])


def offpath(tree, a, b):
    path = embedding(tree, frozenset((a, b)))
    outgoing = []
    def walk(t, p):
        if isinstance(t, int):
            return
        for i, child in enumerate(t):
            q = p + (i,)
            if p in path and q not in path:
                outgoing.append(tuple(sorted(leaves(child))))
            walk(child, q)
    walk(tree, ())
    return outgoing


def hard_pair(tree, other):
    """Only t=2 cherries in either direction; excludes common/t=1/t>=3."""
    return all(len(offpath(y, a, b)) == 2
               for x, y in ((tree, other), (other, tree))
               for a, b in cherries(x))


def baseline_hard_pair(tree, other):
    """Figure16 reaches Whidden(t=2): no earlier printed tree-pair rule."""
    if not hard_pair(tree, other):
        return False
    for x, y in ((tree, other), (other, tree)):
        for a, b in cherries(x):
            side = offpath(y, a, b)
            cy = {frozenset(pair) for pair in cherries(y)}
            if any(len(z) == 1 and (frozenset((z[0], a)) in cy
                                  or frozenset((z[0], b)) in cy) for z in side):
                return False  # Branching rule4.
            blocks = [frozenset(z) for z in side]
            blocks.append(leaves(x) - blocks[0] - blocks[1])
            es = [embedding(x, block) for block in blocks]
            disjoint = all(not (es[i] & es[j]) for i in range(3) for j in range(i))
            homeomorphic = sum(restrict(x, block) == restrict(y, block) for block in blocks)
            if disjoint and homeomorphic >= 2:
                return False  # Lemma13 boundary rule (Figure16 step2d).
    return True


def controls():
    a = node(node(0, 1), node(2, 3))
    t = node(node(0, 1), 2)
    u = node(node(0, 2), 1)
    checks = [
        valid(a, a, ((0, 1, 2, 3),)),
        not valid(t, u, ((0, 1, 2),)),
        optimum(t, u)[0] == 2,
        valid(a, a, ((0,), (1,), (2,), (3,))),
        not valid(a, a, ((0, 2), (1, 3))),
        not valid(a, a, ((0, 1), (1, 2, 3))),
        not valid(a, a, ((0, 1), (2,))),
    ]
    assert all(checks), checks
    return {"passed": sum(checks), "total": len(checks),
            "corruptions_caught": ["wrong topology", "overlap", "duplicate", "missing"]}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=4)
    parser.add_argument("--quotient", action="store_true",
                        help="One first-tree representative per unlabelled rooted shape")
    args = parser.parse_args()
    start = time.monotonic()
    control = controls()
    n = args.n
    ts = trees(tuple(range(n)))
    first_trees = ts
    if args.quotient:
        def shape(t):
            return 0 if isinstance(t, int) else node(shape(t[0]), shape(t[1]))
        representatives = {}
        for t in ts:
            representatives.setdefault(repr(shape(t)), t)
        first_trees = tuple(representatives.values())
    pair_count = 0
    candidate_a = None
    candidate_b = None
    hard_count = 0
    baseline_hard_count = 0
    hard_a = None
    baseline_hard_a = None
    baseline_hard_b = None
    for t in first_trees:
        for u in ts:
            pair_count += 1
            hp = hard_pair(t, u)
            hard_count += hp
            bhp = baseline_hard_pair(t, u)
            baseline_hard_count += bhp
            for a, b in cherries(t):
                side = offpath(u, a, b)
                if len(side) != 2:
                    continue
                if candidate_a is None or (hp and hard_a is None) or (bhp and baseline_hard_a is None):
                    k, forests = optimum(t, u)
                    together = any(any(a in block and b in block for block in f) for f in forests)
                    if not together:
                        restricted_min = min(len(p) for p in all_partitions(tuple(range(n)))
                                             if any(a in block and b in block for block in p)
                                             and valid(t, u, p))
                        witness = {"T": t, "Tprime": u, "cherry": [a, b],
                                   "pendant_sets": side, "optimum_components": k,
                                   "optimum_if_cherry_retained": restricted_min,
                                   "optimal_forests": forests, "hard_pair": hp}
                        if candidate_a is None:
                            candidate_a = witness
                        if hp and hard_a is None:
                            hard_a = witness
                        if bhp and baseline_hard_a is None:
                            baseline_hard_a = witness
                if hp and candidate_b is None:
                    for endpoint in (a, b):
                        keep = leaves(t) - {endpoint}
                        tt, uu = restrict(t, keep), restrict(u, keep)
                        if hard_pair(tt, uu):
                            candidate_b = {"T": t, "Tprime": u, "cherry": [a, b],
                                           "isolated_endpoint": endpoint, "child_T": tt,
                                           "child_Tprime": uu,
                                           "child_cherries": {"T": cherries(tt), "Tprime": cherries(uu)},
                                           "all_child_cherries_t": 2}
                if bhp and baseline_hard_b is None:
                    for endpoint in (a, b):
                        keep = leaves(t) - {endpoint}
                        tt, uu = restrict(t, keep), restrict(u, keep)
                        if baseline_hard_pair(tt, uu):
                            baseline_hard_b = {"T": t, "Tprime": u, "cherry": [a, b],
                                               "isolated_endpoint": endpoint, "child_T": tt,
                                               "child_Tprime": uu,
                                               "scope": "Both states exclude all Figure16 step2a-d rules, checking both orientations."}
    result = {"n": n, "tree_count": len(ts), "first_tree_shapes": len(first_trees),
              "simultaneous_relabeling_quotient": args.quotient, "pairs_checked": pair_count,
              "hard_pairs": hard_count, "controls": control,
              "baseline_hard_pairs": baseline_hard_count,
              "forced_cherry_counterexample": candidate_a,
              "forced_cherry_hard_counterexample": hard_a,
              "forced_cherry_baseline_hard_counterexample": baseline_hard_a,
              "endpoint_lookahead_counterexample": candidate_b,
              "endpoint_lookahead_baseline_hard_counterexample": baseline_hard_b,
              "elapsed_seconds": time.monotonic() - start,
              "scope": "finite exact checks; no universal correctness proof"}
    output = Path(__file__).parents[1] / "results" / f"branching-search-n{n}.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if "counterexample" not in k}, indent=2))
    print("counterexamples", {k: v is not None for k, v in result.items() if "counterexample" in k})


if __name__ == "__main__":
    main()
