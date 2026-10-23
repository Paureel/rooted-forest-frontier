"""One-shot hostile interface checks for CASE-ARGUMENT-v1; not a census.

Uses the permitted existing X0 instrument as-is. This wrapper is retained for
replay, intentionally not registered as a generic rooted-MAF instrument.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "x0"))
from fresh_oracle import Tree, exact, validate_partition


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def partition_key(blocks):
    return sorted(tuple(sorted(b)) for b in blocks)


def cut_witness(tree, blocks):
    count = len(blocks) - 1
    for cuts in itertools.combinations(tree.edges, count):
        produced, empty = tree.cut_blocks(cuts)
        if partition_key(produced) == partition_key(blocks):
            return {"edges": cuts, "blocks": produced, "empty_regions": empty}
    raise AssertionError("no literal original-source cut witness")


def control_checks():
    good = Tree([[1, 2], 3])
    bad = Tree([[1, 3], 2])
    r = exact(good, good)
    assert r["components"] == 1
    wrong = validate_partition(good, bad, [[1, 2, 3]])
    assert not wrong["valid"] and wrong["reason"] == "wrong rooted topology"
    caught = False
    try:
        assert r["components"] == 2, "planted incorrect optimum"
    except AssertionError:
        caught = True
    assert caught
    return {"identical_three_leaf_components": r["components"],
            "wrong_topology_rejected": wrong, "corrupted_optimum_caught": caught}


def geometry(tree, a, b):
    ha, hb = tree.span(a), tree.span(b)
    common = ha & hb
    graph = {v: set() for v in tree.child}
    for u, v in tree.edges:
        graph[u].add(v)
        graph[v].add(u)
    def regions(v, labels):
        occupied = 0
        for neighbor in graph[v]:
            reached, todo = {v, neighbor}, [neighbor]
            while todo:
                w = todo.pop()
                for nxt in graph[w] - reached:
                    reached.add(nxt)
                    todo.append(nxt)
            occupied += bool({tree.leaf[x] for x in labels} & (reached - {v}))
        return occupied
    rows = [{"vertex": v, "A_regions": regions(v, a), "B_regions": regions(v, b),
             "A_degree": len(graph[v] & ha), "B_degree": len(graph[v] & hb)}
            for v in sorted(common)]
    assert common and all(r["A_regions"] == r["B_regions"] == 2 for r in rows)
    assert all(r["A_regions"] == r["A_degree"] and
               r["B_regions"] == r["B_degree"] for r in rows)
    boundaries = []
    for u, v in tree.edges:
        if u not in common or v not in common:
            continue
        below = tree.below[v]
        aa = [a & below, a - below]
        bb = [b & below, b - below]
        assert all(aa) and all(bb)
        a_clear = all(not tree.span(part) & hb for part in aa)
        b_clear = all(not tree.span(part) & ha for part in bb)
        assert a_clear and b_clear
        boundaries.append({"edge": [u, v], "A_colors": [sorted(x) for x in aa],
                           "B_colors": [sorted(x) for x in bb],
                           "A_clear_of_B": a_clear, "B_clear_of_A": b_clear})
    assert boundaries
    return {"shared_vertices": rows, "boundaries": boundaries,
            "root_in_intersection": "" in common}


def case_checks():
    t0 = [[1, [3, 4]], [2, [5, 6]]]
    a, b = frozenset([1, 2]), frozenset([3, 4, 5, 6])
    target = Tree([t0, 7])
    source = Tree([[[1, 2], [[3, 5], [4, 6]]], 7])
    refinement = [[1, 2], [3, 4, 5, 6], [7]]
    geo = geometry(target, a, b)
    root_geo = geometry(Tree(t0), a, b)
    assert root_geo["root_in_intersection"]
    assert source.clusters(a) == target.clusters(a)
    assert source.clusters(b) != target.clusters(b)
    original = [[1], [2], [3, 5], [4], [6], [7]]
    exchanged = [[1, 2], [3], [5], [4], [6], [7]]
    vo = validate_partition(source, target, original, refinement)
    ve = validate_partition(source, target, exchanged, refinement)
    assert vo["valid"] and ve["valid"] and len(exchanged) <= len(original)
    unrestricted = exact(source, target, refinement)
    retained = exact(source, target, refinement, retain_together=a)
    assert retained["components"] == unrestricted["components"]
    b_source = Tree([[3, 5], [4, 6]])
    colors = [[3, 4], [5, 6]]
    one_cut_matches = [e for e in b_source.edges
                       if partition_key(b_source.cut_blocks([e])[0]) == partition_key(colors)]
    assert not one_cut_matches  # false extension from an agreement block to all B
    triple_s, triple_t = Tree([[1, 2], 3]), Tree([[1, 3], 2])
    triple_parts = [[1, 3], [2]]
    triple_valid = validate_partition(triple_s, triple_t, triple_parts)
    triple_opt = exact(triple_s, triple_t)
    assert triple_valid["valid"] and triple_opt["components"] - 1 == 1
    c = Fraction(233, 100)
    p_checks = {str(p): str(Fraction(p, 1) / c ** (2 * (p - 1))) for p in range(2, 7)}
    assert all(Fraction(v) <= 1 / c for v in p_checks.values())
    assert c >= 2 and Fraction(3, 2) / c ** 2 < 1  # base and all later ratios
    false_zero_loss = Fraction(2) > 1 / c
    assert false_zero_loss
    return {"target": target.raw, "source": source.raw, "refinement": refinement,
            "geometry": geo, "root_geometry_control": root_geo,
            "original_partition": vo, "exchanged_partition": ve,
            "original_source_cuts": cut_witness(source, original),
            "exchanged_source_cuts": cut_witness(source, exchanged),
            "unrestricted_optimum": unrestricted, "A_retained_optimum": retained,
            "false_entire_B_one_cut_rejected": {"B_source": b_source.raw,
                "colors": colors, "one_cut_matches": one_cut_matches},
            "one_cut_bad_A_completion": {"source": triple_s.raw, "target": triple_t.raw,
                "partition": triple_parts, "source_cuts": cut_witness(triple_s, triple_parts),
                "components": triple_opt["components"]},
            "p_query_mass_control": {"c": str(c), "target": str(1 / c),
                "p_values": p_checks, "false_zero_loss_bound_rejected": false_zero_loss}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage", choices=["controls", "case"], required=True)
    args = parser.parse_args()
    started = time.perf_counter()
    result = control_checks() if args.stage == "controls" else case_checks()
    payload = {"stage": args.stage, "utc": datetime.now(timezone.utc).isoformat(),
        "elapsed_seconds": time.perf_counter() - started,
        "script_sha256": sha(__file__),
        "x0_sha256": sha(HERE.parent / "x0" / "fresh_oracle.py"),
        "case_sha256": sha(HERE / "CASE-ARGUMENT-v1.md"),
        "result": result, "status": "PASS_FINITE_ONLY"}
    path = HERE / f"referee_case_checks_v1_{args.stage}.json"
    path.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"PASS_FINITE_ONLY stage={args.stage} elapsed={payload['elapsed_seconds']:.6f}s output={path}")
