#!/usr/bin/env python3
"""Compare result data only with the already frozen independent edge-cut engine."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time

from edge_cut import BASE, WORK, catalogue, compare_exact, text_tree, trees, write_json


def partition(forest):
    return tuple(sorted(tuple(sorted(re.findall(r"[^(),]+", comp))) for comp in forest))


def normalized(blocks):
    return tuple(sorted(tuple(sorted(block)) for block in blocks))


if __name__ == "__main__":
    # Registered failure: ANY unequal k, missing/extra generated tree, or missing/
    # extra optimum partition. This comparison does not tune the frozen engine.
    start = time.perf_counter()
    parser = argparse.ArgumentParser()
    parser.add_argument("--oracle", type=Path, default=WORK / "results/oracle-corpus.json")
    parser.add_argument("--output", type=Path, default=WORK / "results/verification-comparison.json")
    parser.add_argument("--plant", action="store_true", help="Do not overwrite the real dashboard progress")
    args = parser.parse_args()
    oracle_path = args.oracle
    oracle_bytes = oracle_path.read_bytes()
    oracle = json.loads(oracle_bytes)
    batches = []
    discrepancies = []
    checked = 0
    for batch in oracle["batches"]:
        n = batch["n"]
        if n > 5:
            continue
        labels = tuple(chr(97 + i) for i in range(n))
        own_trees = trees(labels)
        own_by_key = {text_tree(t): catalogue(t) for t in own_trees}
        external_tree_keys = [text_tree(t) for t in batch["trees"]]
        if set(external_tree_keys) != set(own_by_key) or len(external_tree_keys) != len(own_by_key):
            discrepancies.append({"n": n, "kind": "generated-tree-set-mismatch"})
            continue
        seen_pairs = [(row["a"], row["b"]) for row in batch["cases"]]
        expected_pairs = {(i, j) for i in range(len(own_trees)) for j in range(len(own_trees))}
        if set(seen_pairs) != expected_pairs or len(seen_pairs) != len(expected_pairs):
            discrepancies.append({"n": n, "kind": "incomplete-or-duplicate-pair-coverage",
                                  "actual_pairs": len(seen_pairs), "expected_pairs": len(expected_pairs)})
        for row in batch["cases"]:
            first = own_by_key[external_tree_keys[row["a"]]]
            second = own_by_key[external_tree_keys[row["b"]]]
            shared = first.keys() & second.keys()
            optimum = min(map(len, shared))
            own_partitions = {partition(forest) for forest in shared if len(forest) == optimum}
            external_partitions = {normalized(blocks) for blocks in row["forests"]}
            try:
                compare_exact(optimum, row["k"])
                if own_partitions != external_partitions:
                    raise AssertionError("complete optimum forest partition set differs")
            except AssertionError as exc:
                discrepancies.append({"n": n, "t1": external_tree_keys[row["a"]],
                    "t2": external_tree_keys[row["b"]], "reason": str(exc),
                    "edge_cut_k": optimum, "external_k": row["k"],
                    "edge_cut_partitions": sorted(own_partitions),
                    "external_partitions": sorted(external_partitions)})
            checked += 1
        batches.append({"n": n, "trees": len(own_trees), "ordered_pairs": len(batch["cases"]),
                        "compared": "exact k and complete optimum partition set"})
    result = {"status": "finite-agreement" if not discrepancies else "refuted",
              "ordered_pairs_checked": checked, "batches": batches,
              "discrepancies": discrepancies, "seconds": time.perf_counter()-start,
              "oracle_result_sha256": hashlib.sha256(oracle_bytes).hexdigest(),
              "oracle_generator_sha256": oracle["generator_sha256"],
              "edge_cut_implementation_sha256": hashlib.sha256((BASE / "edge_cut.py").read_bytes()).hexdigest(),
              "comparator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "deepest_shared_layer": "mathematical rooted-MAF definition and Python runtime",
              "scope": "All ordered labelled non-plane rooted binary tree pairs supplied in oracle corpus, n=3..5; finite checks only.",
              "certification_limit": "These discovery cases are not held-out algorithm certification. Agreement does not prove all-size correctness, completeness of a new branching rule, or a smaller exponential bound."}
    write_json(args.output, result)
    progress = json.loads((WORK / "progress/verification.json").read_text())
    progress["status"] = "complete" if not discrepancies else "failed"
    progress["summary"] = f"Independent edge-cut route compared {checked} ordered pairs: {len(discrepancies)} discrepancies. Finite evidence only."
    progress["metrics"]["ordered_pairs_compared"] = checked
    progress["metrics"]["discrepancies"] = len(discrepancies)
    progress["claims"].append({"id": "finite-oracle-agreement", "label": "Separate-route finite comparison",
        "status": "measured" if not discrepancies else "refuted",
        "detail": f"Exact optima and complete optimum partitions on {checked} ordered n=3..5 cases; no universal theorem."})
    progress["artifacts"].append("research/rmaf/results/verification-comparison.json")
    if not args.plant:
        write_json(WORK / "progress/verification.json", progress)
    print(json.dumps({k: result[k] for k in ("status", "ordered_pairs_checked", "seconds", "discrepancies")}))
    if discrepancies:
        raise SystemExit(1)
