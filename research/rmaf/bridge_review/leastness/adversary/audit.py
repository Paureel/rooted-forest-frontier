#!/usr/bin/env python3
"""One-shot RMAF leastness audit; no existing or previous geometry code reused.

Use for the frozen edge/subset comparison only, not a universal theorem.
Outputs exact cases, subsets considered, and perf_counter timings. A failed
assertion stops the audit; success requires ten fixtures and five caught
corruptions including clean twins. All paths remain in this arm's directory.
"""
import argparse
import datetime
import hashlib
import itertools
import json
from pathlib import Path
import time

BASE = Path(__file__).resolve().parent

def graph(tree):
    vertices, edges, labels = [], [], {}
    pending = [(tree, "")]
    while pending:
        item, address = pending.pop()
        vertices.append(address)
        if isinstance(item, int):
            labels[address] = item
        else:
            assert isinstance(item, list) and len(item) == 2
            for bit in (1, 0):
                child = address + str(bit)
                edges.append((address, child))
                pending.append((item[bit], child))
    return vertices, edges, labels

def reached(start, allowed, edges):
    seen, pending = {start}, [start]
    while pending:
        vertex = pending.pop()
        for left, right in edges:
            neighbor = right if left == vertex else left if right == vertex else None
            if neighbor is not None and neighbor in allowed and neighbor not in seen:
                seen.add(neighbor)
                pending.append(neighbor)
    return seen

def connected(vertices, edges):
    return bool(vertices) and reached(next(iter(vertices)), vertices, edges) == vertices

def enumerate_feasible(vertices, edges, terminals):
    vset, feasible, examined = set(vertices), [], 0
    for mask in range(1, 1 << len(vertices)):
        examined += 1
        support = {v for i, v in enumerate(vertices) if mask & (1 << i)}
        if terminals <= support and connected(support, edges):
            feasible.append(support)
    assert feasible
    least = set.intersection(*feasible)
    if terminals:
        assert least in feasible
    return least, feasible, examined

def edge_required(vertices, edges, terminals):
    result = set(terminals)
    for i, (left, right) in enumerate(edges):
        remaining = edges[:i] + edges[i + 1:]
        side = reached(left, set(vertices), remaining)
        assert right not in side
        other = set(vertices) - side
        if side & terminals and other & terminals:
            result.update((left, right))
    return result

def address_edges(support):
    # Adj is unrestricted parent-child adjacency; ambient validity is separate.
    return [(a, b) for a in support for b in support if b and b[:-1] == a]

def classify(support, vertices, terminals, feasible):
    ambient = support <= set(vertices)
    contains = terminals <= support
    conn = connected(support, address_edges(support))
    subset_all = all(support <= other for other in feasible)
    return dict(ambient=ambient, terminals=contains, connected=conn,
                least=ambient and contains and conn and subset_all)

def fixture_run():
    spec = json.loads((BASE / "controls/frozen.json").read_text())
    results, cached = [], {}
    for case in spec["cases"]:
        start = time.perf_counter()
        vertices, edges, labels = graph(case["tree"])
        terminals = {v for v, lab in labels.items() if lab in case["selection"]}
        assert terminals == set(case["terminals"]), case["id"]
        subset_least, feasible, examined = enumerate_feasible(vertices, edges, terminals)
        edge_least = edge_required(vertices, edges, terminals)
        expected = set(case["support"])
        # Empty-terminal root graph has a nonempty-subset intersection {root};
        # the source's empty output is an explicitly separate null convention.
        if terminals:
            assert subset_least == expected == edge_least, case["id"]
        else:
            assert expected == edge_least == set(), case["id"]
        row = dict(id=case["id"], terminal_count=len(terminals),
                   vertex_count=len(vertices), subsets_examined=examined,
                   feasible_count=len(feasible), support=sorted(expected),
                   terminal_nonempty=bool(terminals), seconds=time.perf_counter()-start)
        results.append(row)
        cached[case["id"]] = (case, vertices, terminals, feasible)
    corruption_results = []
    for control in spec["corruptions"]:
        case, vertices, terminals, feasible = cached[control["base"]]
        twin = set(case["support"])
        assert all(classify(twin, vertices, terminals, feasible).values())
        mutant = (twin - set(control["remove"])) | set(control["add"])
        actual = classify(mutant, vertices, terminals, feasible)
        expected = {k: control["expect_" + k] for k in actual}
        assert actual == expected, (control["id"], actual, expected)
        assert not actual["least"]
        corruption_results.append(dict(id=control["id"], actual=actual, twin_pass=True))
    assert len(results) == 10 and len(corruption_results) == 5
    return dict(fixtures=results, corruptions=corruption_results,
                fixture_count=10, caught_corruptions=5, true_twins=5,
                subsets_examined=sum(row["subsets_examined"] for row in results))

def shapes(leaves):
    if leaves == 1:
        yield None
    else:
        for nleft in range(1, leaves):
            for left in shapes(nleft):
                for right in shapes(leaves - nleft):
                    yield (left, right)

def label_shape(shape, labels):
    if shape is None:
        return next(labels)
    return [label_shape(shape[0], labels), label_shape(shape[1], labels)]

def lean_tree(tree):
    return f"(.leaf {tree})" if isinstance(tree, int) else f"(.node {lean_tree(tree[0])} {lean_tree(tree[1])})"

def lean_addresses(addresses):
    return "[" + ", ".join("[" + ", ".join("false" if c == "0" else "true" for c in a) + "]" for a in addresses) + "]"

def corpus_run(bound):
    records, by_bound = [], []
    selections = [[], [0], [1], [0, 1], [2], [0, 0], [1, 1], [0, 1, 0, 1]]
    for n in range(1, bound + 1):
        start, count, examined = time.perf_counter(), 0, 0
        for shape in shapes(n):
            for labels in itertools.product((0, 1), repeat=n):
                tree = label_shape(shape, iter(labels))
                vertices, edges, leaf_labels = graph(tree)
                for selection in selections:
                    terminals = {v for v, lab in leaf_labels.items() if lab in selection}
                    least, feasible, denominator = enumerate_feasible(vertices, edges, terminals)
                    required = edge_required(vertices, edges, terminals)
                    if terminals:
                        assert least == required
                    else:
                        required = set()
                    support = [v for v in vertices if v in required]
                    records.append(dict(tree=tree, selection=selection, support=support,
                                        terminals=sorted(terminals)))
                    count += 1
                    examined += denominator
        by_bound.append(dict(leaves=n, cases=count, subsets_examined=examined,
                             seconds=time.perf_counter()-start))
    expected = sum((1, 1, 2, 5, 14)[n-1] * 2**n * 8 for n in range(1,bound+1))
    assert len(records) == expected
    return records, by_bound

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--bound", type=int, default=0)
    parser.add_argument("--name", default="pilot")
    args = parser.parse_args()
    assert 0 <= args.bound <= 5
    start = time.perf_counter()
    result = dict(timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  fixture_sha256=hashlib.sha256((BASE / "controls/frozen.json").read_bytes()).hexdigest(),
                  pilot=fixture_run())
    if args.bound:
        records, counts = corpus_run(args.bound)
        (BASE / f"results/{args.name}-cases.json").write_text(json.dumps(records, indent=2) + "\n")
        result.update(cases=len(records), bounds=counts)
    result["seconds"] = time.perf_counter() - start
    output = BASE / f"results/{args.name}.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(dict(status="PASS", output=str(output), fixture_count=10,
                         caught_corruptions=5, cases=result.get("cases",0),
                         seconds=result["seconds"])))

if __name__ == "__main__":
    main()
