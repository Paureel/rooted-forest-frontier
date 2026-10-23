#!/usr/bin/env python3
"""One-shot independent BFS/leaf-support replay of frozen family controls.

No author implementation is imported. Exact disagreements are failures. This
checks only registered tiny examples, not universal Lean or Python correctness.
"""
import argparse
from collections import deque
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import time


def tree_graph(tree):
    graph, labels = {}, {}

    def visit(t, address):
        graph[address] = set()
        if isinstance(t, str):
            if t in labels.values():
                raise ValueError("duplicate leaf label")
            labels[address] = t
        else:
            assert isinstance(t, list) and len(t) == 2
            for bit, child in zip("01", t):
                v = address + bit
                visit(child, v)
                graph[address].add(v)
                graph[v].add(address)

    visit(tree, "")
    return graph, labels


def path(graph, start, finish):
    queue, parent = deque([start]), {start: None}
    while queue:
        v = queue.popleft()
        if v == finish:
            route = set()
            while v is not None:
                route.add(v)
                v = parent[v]
            return route
        for w in graph[v]:
            if w not in parent:
                parent[w] = v
                queue.append(w)
    raise ValueError("disconnected graph")


def span(graph, seeds):
    seeds = set(seeds)
    return set().union(*(path(graph, a, b) for a in seeds for b in seeds))


def convex(graph, support):
    support = set(support)
    return support <= graph.keys() and span(graph, support) <= support


def lca_closed(support):
    for a in support:
        for b in support:
            i = 0
            while i < min(len(a), len(b)) and a[i] == b[i]:
                i += 1
            if a[:i] not in support:
                return False
    return True


def valid(graph, labels, closed, opened, retained):
    supports = closed + ([] if opened is None else [opened])
    if any(not convex(graph, s) for s in supports):
        return False
    if any("" in s or not (set(s) & labels.keys()) for s in closed):
        return False
    if opened is not None and ("" not in opened or (retained and not (set(opened) & labels.keys()))):
        return False
    if any(set(a) & set(b) for i, a in enumerate(supports) for b in supports[i + 1:]):
        return False
    return all(sum(v in s for s in supports) == 1 for v in labels)


def normalize(graph, labels, closed, opened):
    trimmed = [span(graph, set(s) & labels.keys()) for s in closed]
    live = None if opened is None else set(opened) & labels.keys()
    return trimmed, span(graph, live | {""}) if live else None


def blocks(labels, closed, opened):
    supports = closed + ([] if opened is None else [opened])
    return [sorted(labels[v] for v in s if v in labels) for s in supports if set(s) & labels.keys()]


def exact(actual, expected, where):
    if actual != expected:
        raise AssertionError(f"{where}: actual={actual!r}, expected={expected!r}")


def serial(supports):
    return [sorted(s) for s in supports]


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--out", type=Path, required=True)
    args = p.parse_args()
    base = Path(__file__).resolve().parent.parent
    started = datetime.now(timezone.utc).isoformat()
    clock = time.perf_counter()
    g, lab = tree_graph("a")
    cl, op = normalize(g, lab, [], {""})
    exact((serial(cl), sorted(op), len(cl), len(blocks(lab, cl, op))), ([], [""], 0, 1), "singleton plant")
    caught = None
    try:
        exact(len(cl), 1, "planted false singleton charge")
    except AssertionError as exc:
        caught = str(exc)
    assert caught is not None
    exact(len(cl), 0, "clean singleton charge twin")
    pilot = time.perf_counter() - clock
    v1 = json.loads((base / "controls.json").read_text())
    v2 = json.loads((base / "controls-amendment-v2.json").read_text())
    rows = v1["known_regressions"] + v1["new_controls"] + v1["malformed_or_corrupt"]
    lookup = {r["id"]: r for r in rows}
    results = []
    for row in rows:
        result = {"id": row["id"]}
        if "tree" in row:
            g, lab = tree_graph(row["tree"])
        if "region" in row:
            result.update(lca_closed=lca_closed(row["region"]), path_convex=convex(g, row["region"]))
            for key in ("lca_closed", "path_convex"):
                exact(result[key], row[key], row["id"] + ":" + key)
        if "regions" in row:
            old = [set(s) for s in row["regions"]]
            oi = row["open"]
            closed = [s for i, s in enumerate(old) if i != oi]
            opened = None if oi is None else old[oi]
            ok = valid(g, lab, closed, opened, retained=True)
            result["retained_valid"] = ok
            exact(ok, row.get("family_valid", True), row["id"] + ":valid")
            if ok:
                nc, no = normalize(g, lab, closed, opened)
                assert valid(g, lab, nc, no, retained=True)
                before_blocks = blocks(lab, closed, opened)
                after_blocks = blocks(lab, nc, no)
                exact(after_blocks, before_blocks, row["id"] + ":labels")
                assert len({tuple(b) for b in after_blocks}) == len(after_blocks)
                result.update(closed_cost=len(nc), blocks=len(after_blocks), block_labels=after_blocks)
                if "trimmed" in row:
                    iterator = iter(nc)
                    ordered = [no if i == oi else next(iterator) for i in range(len(old))]
                    result["trimmed"] = serial(ordered)
                    exact(result["trimmed"], [sorted(s) for s in row["trimmed"]], row["id"] + ":normalization")
                for key in ("closed_cost", "blocks"):
                    if key in row:
                        exact(result[key], row[key], row["id"] + ":" + key)
                if "right_fragment" in row:
                    subtree = {v for v in g if v.startswith("1")}
                    fragment = opened & subtree
                    result["right_fragment"] = sorted(fragment)
                    result["right_fragment_labels"] = sorted(lab[v] for v in fragment if v in lab)
                    exact(result["right_fragment"], row["right_fragment"], "fragment")
                    exact(result["right_fragment_labels"], row["right_fragment_labels"], "fragment labels")
                    result["right_fragment_must_be_discarded"] = not bool(result["right_fragment_labels"])
                    result["charged_blocks_added"] = int(bool(result["right_fragment_labels"]))
                    for key in ("right_fragment_must_be_discarded", "charged_blocks_added"):
                        exact(result[key], row[key], key)
                if "bad_colors" in row:
                    labels_all = set().union(*(set(b) for b in after_blocks))
                    merged_valid = not any(set(bad) <= labels_all for bad in row["bad_colors"])
                    assert all(not any(set(bad) <= set(block) for bad in row["bad_colors"]) for block in after_blocks)
                    result["merged_full_color_valid"] = merged_valid
                    exact(merged_valid, row["merged_full_color_valid"], "merged color")
        if row["id"] == "drop-open-stem-mutant":
            g, lab = tree_graph(lookup[row["control"]]["tree"])
            result["mutant_path_convex"] = convex(g, row["mutant_support"])
            result["clean_twin_path_convex"] = convex(g, row["clean_twin_support"])
            exact(result["mutant_path_convex"], row["path_convex"], "stem mutant")
            exact(result["clean_twin_path_convex"], True, "stem clean twin")
        if row["id"] == "charge-empty-fragment-mutant":
            expected = next(r["charged_blocks_added"] for r in results if r["id"] == row["control"])
            exact(expected, row["expected_added_charge"], "empty fragment cost twin")
            assert row["mutant_added_charge"] != expected
            result.update(mutant_added_charge=row["mutant_added_charge"], actual_added_charge=expected, mutant_rejected=True, clean_twin_accepted=True)
        result["passed"] = True
        results.append(result)
    for row in v2["controls"]:
        result = {"id": row["id"]}
        if "tree" in row:
            g, lab = tree_graph(row["tree"])
            closed, opened = [set(s) for s in row["closed"]], set(row["open"])
            raw_valid = valid(g, lab, closed, opened, retained=False)
            exact(raw_valid, row.get("raw_valid", True), "raw validity")
            nc, no = normalize(g, lab, closed, opened)
            result.update(raw_valid=raw_valid,
                          retained_valid_before_pruning=valid(g, lab, closed, opened, retained=True),
                          normalized_closed=serial(nc), normalized_open=None if no is None else sorted(no),
                          closed_cost_before=len(closed), closed_cost_after=len(nc),
                          labelled_blocks_before=len(blocks(lab, closed, opened)), labelled_blocks_after=len(blocks(lab, nc, no)),
                          raw_support_objects_before=len(closed) + 1, raw_support_objects_after=len(nc) + int(no is not None))
            assert valid(g, lab, nc, no, retained=True)
            exact(blocks(lab, closed, opened), blocks(lab, nc, no), "v2 block labels")
            for key, expected in row.items():
                if key in result:
                    exact(result[key], expected, row["id"] + ":" + key)
        else:
            actual = next(r["closed_cost_after"] for r in results if r["id"] == "raw-empty-open")
            exact(actual, row["expected_cost"], "v2 expected cost")
            exact(actual, row["clean_twin_cost"], "v2 clean cost twin")
            assert actual != row["mutant_cost"]
            result.update(actual_cost=actual, mutant_cost=row["mutant_cost"], mutant_rejected=True, clean_twin_accepted=True)
        result["passed"] = True
        results.append(result)
    exact(len(results), 17, "registered row count")
    receipt = {"schema": 1, "started_utc": started, "runtime_seconds": time.perf_counter() - clock,
               "pilot_seconds": pilot, "planted_false_diagnostic": caught, "planted_clean_twin_passed": True,
               "method": "direct undirected graph BFS paths and leaf-label sets; no author helper import",
               "scope": "17 registered rows, no census, not a universal theorem or executable correctness proof",
               "inputs_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
                                 [base / "controls.json", base / "controls-amendment-v2.json", Path(__file__)]},
               "rows": results, "passed_rows": len(results)}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"passed_rows": len(results), "pilot_seconds": pilot,
                      "runtime_seconds": receipt["runtime_seconds"], "receipt": str(args.out)}))


if __name__ == "__main__":
    main()
