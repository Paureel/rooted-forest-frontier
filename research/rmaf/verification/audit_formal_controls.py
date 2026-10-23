#!/usr/bin/env python3
"""Independent edge-deletion check of finite controls read from the formal core.

The edge-cut engine was frozen and executed before the formal core was read.
This script does not import Lean code or any discovery evaluator.
"""
import json

from edge_cut import BASE, WORK, catalogue, common_solution, write_json
from compare_results import partition


if __name__ == "__main__":
    left = (("a", "b"), ("c", "d"))
    right = (("a", ("b", "c")), "d")
    first, second = catalogue(left), catalogue(right)
    shared = first.keys() & second.keys()
    optimum = min(map(len, shared))
    singleton_endpoints = [forest for forest in shared if "a" in forest or "b" in forest]
    endpoint_cost = min(map(len, singleton_endpoints))
    witness = ("((a,b),d)", "c")
    overlapping_pairs = ("(a,c)", "(b,d)")
    assert optimum == 2
    assert endpoint_cost == 3
    assert witness in shared
    assert overlapping_pairs not in first
    assert ("a", "b", "c", "d") in shared
    result = {"status": "finite-control-confirmed", "tree_pair": [left, right],
              "k": optimum, "minimum_with_a_or_b_isolated": endpoint_cost,
              "all_optimum_partitions": sorted(partition(forest) for forest in shared if len(forest) == optimum),
              "optimum_witness": {"forest": witness, "cut_masks": [first[witness], second[witness]]},
              "overlap_control": {"forest": overlapping_pairs, "accepted": False},
              "singletons_accepted": True,
              "claim": "This exact finite instance refutes an endpoint-isolation-only branching rule.",
              "scope": "One concrete no-rho ordinary rooted-MAF instance; no general branching rule or complexity improvement follows."}
    write_json(WORK / "results/verification-formal-controls.json", result)
    print(json.dumps({k: result[k] for k in ("status", "k", "minimum_with_a_or_b_isolated", "all_optimum_partitions")}))
