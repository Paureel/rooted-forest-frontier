#!/usr/bin/env python3
"""Problem-local independent rMAF verification instrument, not a faster FPT algorithm.

New code is needed because the consulted BootLoops index covers exact algebra
and phylogenetic likelihoods, but no rooted agreement-forest enumerator. Its
purpose is to provide a structurally separate edge-deletion route for this
campaign; no discovery evaluator is imported or read.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
import hashlib
from itertools import combinations_with_replacement
import json
from pathlib import Path
import time

BASE = Path(__file__).resolve().parent
WORK = BASE.parent


def text_tree(tree):
    if isinstance(tree, str):
        return tree
    a, b = sorted((text_tree(tree[0]), text_tree(tree[1])))
    return f"({a},{b})"


def validate_tree(tree):
    if isinstance(tree, str):
        if not tree or any(c in tree for c in "(),; "):
            raise ValueError("invalid leaf label")
        return [tree]
    if not isinstance(tree, (tuple, list)) or len(tree) != 2:
        raise ValueError("input must be a rooted binary tree")
    labels = validate_tree(tree[0]) + validate_tree(tree[1])
    if len(set(labels)) != len(labels):
        raise ValueError("duplicate leaf label")
    return labels


def validate_pair(t1, t2):
    if set(validate_tree(t1)) != set(validate_tree(t2)):
        raise ValueError("leaf labels differ")


def linearize(tree):
    """Allocate fresh vertex ids and an oriented edge index for this input."""
    vertices = []
    edges = []

    def walk(node, parent=None):
        vertex = len(vertices)
        vertices.append({"label": node if isinstance(node, str) else None,
                         "parent": parent, "children": []})
        if parent is not None:
            edge = len(edges)
            edges.append((parent, vertex))
            vertices[parent]["children"].append((vertex, edge))
        if not isinstance(node, str):
            walk(node[0], vertex)
            walk(node[1], vertex)
        return vertex

    walk(tree)
    return vertices, edges


def cut_forest(vertices, edges, mask):
    """Connected components after edge deletion; trim empties, suppress unary nodes."""
    roots = [0] + [child for edge, (_, child) in enumerate(edges)
                   if (mask >> edge) & 1]

    def reduce_vertex(v):
        node = vertices[v]
        if node["label"] is not None:
            return node["label"]
        children = [reduce_vertex(child) for child, edge in node["children"]
                    if not ((mask >> edge) & 1)]
        children = [child for child in children if child is not None]
        if not children:
            return None
        if len(children) == 1:
            return children[0]
        return "(" + ",".join(sorted(children)) + ")"

    return tuple(sorted(comp for root in roots
                        if (comp := reduce_vertex(root)) is not None))


def catalogue(tree):
    validate_tree(tree)
    vertices, edges = linearize(tree)
    forests = {}
    for mask in range(1 << len(edges)):
        forest = cut_forest(vertices, edges, mask)
        old = forests.get(forest)
        if old is None or mask.bit_count() < old.bit_count():
            forests[forest] = mask
    return forests


def solve(t1, t2):
    validate_pair(t1, t2)
    return common_solution(catalogue(t1), catalogue(t2))


def common_solution(first, second):
    shared = first.keys() & second.keys()
    forest = min(shared, key=lambda f: (len(f), f))
    return {"k": len(forest), "forest": list(forest),
            "cut_masks": [first[forest], second[forest]],
            "cut_counts": [first[forest].bit_count(), second[forest].bit_count()]}


@lru_cache(None)
def trees(labels):
    """Independent label-split generator: first label fixes the unordered symmetry."""
    labels = tuple(labels)
    if len(labels) == 1:
        return (labels[0],)
    rest = labels[1:]
    answer = []
    for membership in range((1 << len(rest)) - 1):
        left = (labels[0],) + tuple(x for i, x in enumerate(rest)
                                    if (membership >> i) & 1)
        right = tuple(x for i, x in enumerate(rest)
                      if not ((membership >> i) & 1))
        for a in trees(left):
            for b in trees(right):
                answer.append(tuple(sorted((a, b), key=text_tree)))
    return tuple(sorted(answer, key=text_tree))


def compare_exact(left, right):
    if not isinstance(left, int) or not isinstance(right, int) or left != right:
        raise AssertionError(f"exact integer mismatch: {left!r} != {right!r}")
    return True


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + ".tmp")
    temp.write_text(json.dumps(data, indent=2) + "\n")
    temp.replace(path)


def update(summary, metrics, status="running"):
    write_json(WORK / "progress/verification.json", {
        "id": "verification", "title": "Independent verification", "status": status,
        "summary": summary, "metrics": metrics,
        "claims": [{"id": "edge-cut-checker", "label": "Exact edge-cut evaluator",
                    "status": "measured" if metrics.get("controls_executed") else "open",
                    "detail": "Finite exact checks only; no universal correctness or smaller-base proof."}],
        "lemmas": [], "artifacts": ["research/rmaf/verification/JOURNAL.md",
            "research/rmaf/verification/edge_cut.py", "research/rmaf/results/verification-controls.json",
            "research/rmaf/results/verification-corpus.json"]})


def controls():
    fixture = json.loads((BASE / "controls.json").read_text())
    rows = []
    for case in fixture["cases"]:
        result = solve(case["t1"], case["t2"])
        compare_exact(result["k"], case["expected_k"])
        rows.append({"id": case["id"], "expected_k": case["expected_k"],
                     "result": result, "passed": True})
    for case in fixture["rejections"]:
        try:
            solve(case["t1"], case["t2"])
        except ValueError as exc:
            rows.append({"id": case["id"], "rejected": True, "reason": str(exc)})
        else:
            raise AssertionError("corruption accepted: " + case["id"])
    planted = fixture["planted_comparison"]
    try:
        compare_exact(planted["left"], planted["right"])
    except AssertionError as exc:
        rows.append({"id": "planted-wrong-comparison", "rejected": True, "reason": str(exc)})
    else:
        raise AssertionError("comparison accepted a planted wrong answer")
    record = {"method": "independent edge-subset enumeration", "rows": rows,
              "fixture_sha256": hashlib.sha256((BASE / "controls.json").read_bytes()).hexdigest(),
              "implementation_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    write_json(WORK / "results/verification-controls.json", record)
    print(json.dumps({"controls_executed": len(rows), "status": "all expected outcomes observed"}), flush=True)
    return len(rows)


def run_corpus(max_n):
    num_controls = controls()
    rows = []
    timings = []
    for n in range(3, max_n + 1):
        start = time.perf_counter()
        labels = tuple(chr(97 + i) for i in range(n))
        generated = trees(labels)
        if len(set(map(text_tree, generated))) != len(generated):
            raise AssertionError("duplicate generated trees")
        catalogue_start = time.perf_counter()
        catalogues = [catalogue(tree) for tree in generated]
        catalogue_seconds = time.perf_counter() - catalogue_start
        histogram = {}
        for i, j in combinations_with_replacement(range(len(generated)), 2):
            result = common_solution(catalogues[i], catalogues[j])
            rows.append({"n": n, "t1": text_tree(generated[i]), "t2": text_tree(generated[j]), **result})
            histogram[result["k"]] = histogram.get(result["k"], 0) + 1
        timing = {"n": n, "trees": len(generated), "edge_masks_per_tree": 1 << (2*n-2),
                  "pairs": len(generated) * (len(generated)+1)//2,
                  "catalogue_seconds": catalogue_seconds, "seconds": time.perf_counter()-start,
                  "histogram": histogram}
        timings.append(timing)
        write_json(WORK / "results/verification-corpus.json", {
            "method": "independent edge-subset enumeration", "scope": "all unordered labelled non-plane rooted binary tree pairs n=3.."+str(n),
            "implementation_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "timings": timings, "rows": rows,
            "limitation": "Finite exact testing, not held-out algorithm certification or a theorem for arbitrary n."})
        update(f"Exact edge-cut catalogue complete through n={n}; {len(rows)} pairs retained.",
               {"controls_executed": num_controls, "pairs_checked": len(rows), "max_n": n})
        print(json.dumps(timing), flush=True)
    update(f"Finite edge-cut enumeration complete: {len(rows)} pairs; external comparison pending.",
           {"controls_executed": num_controls, "pairs_checked": len(rows), "max_n": max_n}, "waiting")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=4)
    args = parser.parse_args()
    run_corpus(args.max_n)
