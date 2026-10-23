#!/usr/bin/env python3
"""Problem-specific rooted-MAF discovery oracle; not a universal proof.

Enumerates leaf partitions, comparing rooted restrictions and minimal vertex
embeddings. Existing BootLoops tools were consulted: none implements rooted
agreement-forest combinatorics; Annihilator handles holonomic recurrences and
JaCK & Jill handles Bayesian phylogenetic evidence rather than this problem.
This instrument lives with the rMAF experiment intentionally, preserving the
upstream toolkit and pins. See README.md for convention and acceptance limits.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
from functools import lru_cache
import hashlib
from itertools import combinations
import json
from pathlib import Path
import sys
import time

try:
    from telemetry import step, metric, gate, artifact
except ImportError:
    from contextlib import nullcontext
    def step(*args, **kwargs): return nullcontext()
    def metric(*args, **kwargs): pass
    def gate(*args, **kwargs): pass
    def artifact(*args, **kwargs): pass

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
RESULTS = ROOT / "research/rmaf/results"
PROGRESS = ROOT / "research/rmaf/progress/oracle.json"
CONVENTION = "ordinary rooted binary non-plane leaf-labelled trees, no rho; k=components"


class Invalid(ValueError):
    def __init__(self, reason, detail):
        super().__init__(detail)
        self.reason, self.detail = reason, detail


def order_key(t):
    return (0, t) if isinstance(t, str) else (1, order_key(t[0]), order_key(t[1]))


def parse_tree(raw):
    seen = set()
    def rec(value):
        if isinstance(value, str) and value:
            if value in seen:
                raise Invalid("tree-duplicate-label", value)
            seen.add(value)
            return value
        if not isinstance(value, (list, tuple)) or len(value) != 2:
            raise Invalid("tree-nonbinary", repr(value))
        return tuple(sorted((rec(value[0]), rec(value[1])), key=order_key))
    return rec(raw)


def labels(t):
    if isinstance(t, str): return frozenset((t,))
    return labels(t[0]) | labels(t[1])


def pair(raw_a, raw_b):
    a, b = parse_tree(raw_a), parse_tree(raw_b)
    if labels(a) != labels(b):
        raise Invalid("tree-label-set", "Input leaf-label sets differ")
    return a, b


def restriction(t, subset):
    if isinstance(t, str): return t if t in subset else None
    a, b = restriction(t[0], subset), restriction(t[1], subset)
    if a is None: return b
    if b is None: return a
    return tuple(sorted((a, b), key=order_key))


class TreeData:
    def __init__(self, t):
        self.tree = t
        self.labels = tuple(sorted(labels(t)))
        self.paths = {}
        self.edges = []
        self.vertices = []
        def walk(subtree, path, ancestors):
            self.vertices.append(path)
            chain = ancestors + (path,)
            if isinstance(subtree, str):
                self.paths[subtree] = chain
            else:
                for child, branch in zip(subtree, ("0", "1")):
                    next_path = path + branch
                    self.edges.append((path, next_path))
                    walk(child, next_path, chain)
        walk(t, "", ())
        self.bit = {v: 1 << i for i, v in enumerate(self.vertices)}
        self.restrictions, self.embeddings = {}, {}
        for length in range(1, len(self.labels) + 1):
            for block in combinations(self.labels, length):
                self.restrictions[block] = restriction(t, frozenset(block))
                chains = [self.paths[x] for x in block]
                common = 0
                for idx in range(min(map(len, chains))):
                    if len({chain[idx] for chain in chains}) != 1: break
                    common = idx
                vertices = {v for chain in chains for v in chain[common:]}
                self.embeddings[block] = sum(self.bit[v] for v in vertices)

    def disjoint(self, forest):
        used = 0
        for block in forest:
            mask = self.embeddings[block]
            if used & mask: return False
            used |= mask
        return True

    def cut_witness(self, forest):
        """Extend disjoint minimal embeddings to connected vertex regions."""
        owner = {}
        for i, block in enumerate(forest):
            mask = self.embeddings[block]
            for v in self.vertices:
                if mask & self.bit[v]:
                    assert v not in owner
                    owner[v] = i
        neighbors = {v: [] for v in self.vertices}
        for u, v in self.edges:
            neighbors[u].append(v)
            neighbors[v].append(u)
        queue = deque(sorted(owner, key=lambda v: (owner[v], v)))
        while queue:
            u = queue.popleft()
            for v in sorted(neighbors[u]):
                if v not in owner:
                    owner[v] = owner[u]
                    queue.append(v)
        cuts = [(u, v) for u, v in self.edges if owner[u] != owner[v]]
        assert len(cuts) == len(forest) - 1
        for leaf, chain in self.paths.items():
            assert leaf in forest[owner[chain[-1]]]
        return [{"parent": u or "root", "child": v, "parent_block": owner[u], "child_block": owner[v]} for u, v in cuts]


def canonical_forest(raw, expected):
    if not isinstance(raw, list) or not raw:
        raise Invalid("empty-forest", "Expected nonempty list of blocks")
    flattened = []
    for block in raw:
        if not isinstance(block, list) or not block:
            raise Invalid("empty-block", "Every component must be nonempty")
        if not all(isinstance(x, str) and x for x in block):
            raise Invalid("invalid-label", repr(block))
        flattened.extend(block)
    counts = Counter(flattened)
    duplicates = sorted(x for x, count in counts.items() if count > 1)
    if duplicates: raise Invalid("duplicate-label", ",".join(duplicates))
    if set(flattened) != set(expected):
        raise Invalid("label-coverage", f"missing={sorted(set(expected)-set(flattened))}; extra={sorted(set(flattened)-set(expected))}")
    return tuple(sorted(tuple(sorted(block)) for block in raw))


def validate(a, b, raw_forest):
    da, db = TreeData(a), TreeData(b)
    try:
        forest = canonical_forest(raw_forest, da.labels)
        for block in forest:
            if da.restrictions[block] != db.restrictions[block]:
                raise Invalid("restriction-mismatch", f"block={block}")
        for name, data in (("a", da), ("b", db)):
            for x, y in combinations(forest, 2):
                overlap = data.embeddings[x] & data.embeddings[y]
                if overlap:
                    nodes = [v or "root" for v in data.vertices if data.bit[v] & overlap]
                    raise Invalid("embedding-overlap", f"tree={name}; blocks={x},{y}; vertices={nodes}")
        return {"valid": True, "forest": forest, "k": len(forest), "cuts_a": da.cut_witness(forest), "cuts_b": db.cut_witness(forest)}
    except Invalid as error:
        return {"valid": False, "reason": error.reason, "detail": error.detail}


@lru_cache(None)
def partitions(leaf_tuple):
    """Restricted-growth construction: each set partition exactly once."""
    result = []
    def visit(idx, blocks):
        if idx == len(leaf_tuple):
            result.append(tuple(tuple(block) for block in blocks))
            return
        x = leaf_tuple[idx]
        for i in range(len(blocks)):
            blocks[i].append(x)
            visit(idx + 1, blocks)
            blocks[i].pop()
        blocks.append([x])
        visit(idx + 1, blocks)
        blocks.pop()
    visit(0, [])
    return tuple(sorted(result, key=lambda f: (len(f), f)))


@lru_cache(None)
def all_trees(leaf_tuple):
    if len(leaf_tuple) == 1: return (leaf_tuple[0],)
    result = []
    first, rest = leaf_tuple[0], leaf_tuple[1:]
    for length in range(len(rest)):
        for extra in combinations(rest, length):
            left = (first,) + extra
            right = tuple(x for x in rest if x not in extra)
            for a in all_trees(left):
                for b in all_trees(right):
                    result.append(tuple(sorted((a, b), key=order_key)))
    return tuple(sorted(result, key=order_key))


def optimum(a, b, all_optima=False, data=None):
    da, db = data or (TreeData(a), TreeData(b))
    found, tested = [], 0
    for forest in partitions(da.labels):
        if found and len(forest) > len(found[0]): break
        tested += 1
        if not da.disjoint(forest) or not db.disjoint(forest): continue
        if all(da.restrictions[block] == db.restrictions[block] for block in forest):
            found.append(forest)
            if not all_optima: break
    assert found, "Singleton forest must be valid for every valid pair"
    return {"k": len(found[0]), "forests": found, "partitions_tested": tested}


def cherries(t):
    if isinstance(t, str): return ()
    here = (tuple(sorted(t)),) if all(isinstance(c, str) for c in t) else ()
    return here + cherries(t[0]) + cherries(t[1])


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def update_progress(summary, metrics, claims=None, example=None, status="working"):
    old = json.loads(PROGRESS.read_text()) if PROGRESS.exists() else {}
    old.update(id="oracle", title="Exact small-instance oracle", status=status, summary=summary, metrics=metrics)
    if claims is not None: old["claims"] = claims
    if example is not None: old["example"] = example
    old.setdefault("lemmas", [])
    old["artifacts"] = ["research/rmaf/oracle/README.md", "research/rmaf/results/oracle-controls.json", "research/rmaf/results/oracle-corpus.json", "research/rmaf/results/oracle-local-rules.json"]
    write_json(PROGRESS, old)


def controls():
    fixture_path = HERE / "controls.json"
    fixture = json.loads(fixture_path.read_text())
    checks = []
    with step("check", tool="rmaf-oracle"):
        for case in fixture["optima"]:
            a, b = pair(case["a"], case["b"])
            result = optimum(a, b, all_optima=True)
            assert result["k"] == case["k"], (case["id"], result)
            witness = validate(a, b, [list(block) for block in result["forests"][0]])
            assert witness["valid"]
            checks.append({"id": case["id"], "passed": True, "expected_k": case["k"], "actual": result, "witness": witness})
        for case in fixture["forests"]:
            a, b = pair(case["a"], case["b"])
            result = validate(a, b, case["forest"])
            assert result["valid"] == case["valid"], (case["id"], result)
            if not case["valid"]: assert result["reason"] == case["reason"], (case["id"], result)
            checks.append({"id": case["id"], "passed": True, "expected_valid": case["valid"], "actual": result})
        for case in fixture["input_corruptions"]:
            try:
                pair(case["a"], case["b"])
            except Invalid as error:
                assert error.reason == case["reason"]
                checks.append({"id": case["id"], "passed": True, "actual": {"reason": error.reason, "detail": error.detail}})
            else: raise AssertionError(f"Missed corruption {case['id']}")
    receipt = {"convention": CONVENTION, "fixture_sha256": sha(fixture_path), "generator_sha256": sha(Path(__file__)), "checks_passed": len(checks), "checks_expected": 15, "checks": checks, "status": "executed-exact-not-Lean"}
    assert len(checks) == receipt["checks_expected"]
    write_json(RESULTS / "oracle-controls.json", receipt)
    gate("known_truth", "passed", detail="15/15 frozen hand controls and deliberate corruptions; research/rmaf/results/oracle-controls.json")
    artifact("research/rmaf/results/oracle-controls.json")
    print(json.dumps({"controls": f"{len(checks)}/15", "status": receipt["status"]}))
    return receipt


def corpus(ns):
    control_receipt = controls()  # Every real run first proves its controls still work.
    report = {"convention": CONVENTION, "generator_sha256": sha(Path(__file__)), "controls_sha256": sha(HERE / "controls.json"), "controls_passed": control_receipt["checks_passed"], "batches": [], "status": "executed-exact-not-Lean"}
    counterexamples, endpoint_tests, tested_partitions = [], 0, 0
    total_cases = 0
    example = None
    with step("compute", tool="rmaf-oracle"):
        for n in ns:
            leaf_tuple = tuple(chr(ord("a") + i) for i in range(n))
            trees = all_trees(leaf_tuple)
            datas = [TreeData(t) for t in trees]
            cases, histogram = [], Counter()
            start = time.perf_counter()
            for i, a in enumerate(trees):
                for j, b in enumerate(trees):
                    result = optimum(a, b, all_optima=True, data=(datas[i], datas[j]))
                    tested_partitions += result["partitions_tested"]
                    histogram[result["k"]] += 1
                    cases.append({"a": i, "b": j, "k": result["k"], "forests": result["forests"]})
                    b_cherries = cherries(b)
                    for cherry in cherries(a):
                        if cherry in b_cherries: continue
                        endpoint_tests += 1
                        if not any((cherry[0],) in f or (cherry[1],) in f for f in result["forests"]):
                            if not counterexamples:
                                counterexamples.append({"rule": "endpoint-only-cherry", "a": a, "b": b, "cherry": cherry, "k": result["k"], "all_optimal_forests": result["forests"], "witness": validate(a, b, [list(block) for block in result["forests"][0]])})
                    if example is None and n == 4 and result["k"] == 3:
                        example = {"tree_a": a, "tree_b": b, "forest": result["forests"][0], "k": result["k"], "caption": "Exact partition enumeration: three components are necessary for this pair."}
                        witness = validate(a, b, [list(block) for block in result["forests"][0]])
                        write_json(RESULTS / "oracle-example.json", {**example, "witness": witness, "convention": CONVENTION, "status": "executed-exact-not-Lean"})
                    if len(cases) % 100 == 0:
                        metric("completed", total_cases + len(cases), unit="tree pairs")
                        update_progress(f"Enumerating all ordered pairs on {n} leaves; testing a quantified cherry rule.", {"pairs": total_cases + len(cases), "partitions": tested_partitions, "endpoint_tests": endpoint_tests}, example=example)
            elapsed = time.perf_counter() - start
            total_cases += len(cases)
            batch = {"n": n, "tree_count": len(trees), "ordered_pairs_expected": len(trees)**2, "ordered_pairs_completed": len(cases), "partition_count": len(partitions(leaf_tuple)), "seconds": elapsed, "pairs_per_second": len(cases)/elapsed, "optimum_histogram": dict(sorted(histogram.items())), "trees": trees, "cases": cases}
            assert len(cases) == batch["ordered_pairs_expected"]
            report["batches"].append(batch)
            write_json(RESULTS / "oracle-corpus.json", report)
            print(json.dumps({k: batch[k] for k in ("n", "tree_count", "ordered_pairs_completed", "partition_count", "seconds", "optimum_histogram")}))
    # A deliberately over-general reduction has a hand-known small killer.
    a, b = pair([["a", "b"], "c"], [["a", "c"], "b"])
    before = optimum(a, b, all_optima=True)
    keep = frozenset(("a", "c"))
    after_a, after_b = restriction(a, keep), restriction(b, keep)
    after = optimum(after_a, after_b, all_optima=True)
    assert restriction(a, frozenset(("a", "b"))) == restriction(b, frozenset(("a", "b")))
    assert before["k"] != after["k"]
    counterexamples.append({"rule": "restriction-only-contraction", "a": a, "b": b, "equal_restricted_block": ["a", "b"], "retained_label": "a", "before": before, "after_a": after_a, "after_b": after_b, "after": after, "mechanism": "Equality of a restriction does not make its embedding pendant in both inputs."})
    rules_report = {"convention": CONVENTION, "rule_spec_sha256": sha(HERE / "local-rules.json"), "endpoint_rule_tests": endpoint_tests, "counterexamples": counterexamples, "endpoint_rule_status": "refuted-by-exact-enumeration" if any(c["rule"] == "endpoint-only-cherry" for c in counterexamples) else "no-counterexample-on-tested-corpus-not-proved", "status": "executed-exact-not-Lean"}
    write_json(RESULTS / "oracle-local-rules.json", rules_report)
    for path in ("oracle-corpus.json", "oracle-local-rules.json", "oracle-example.json"):
        artifact("research/rmaf/results/" + path)
    claims = [
        {"id": "frozen-controls", "label": "Frozen controls", "status": "tested", "detail": "15/15 hand controls, invalid forests, and malformed inputs passed. Exact Python checks; not Lean."},
        {"id": "small-corpus", "label": "Complete small corpus", "status": "tested", "detail": f"{total_cases} ordered tree pairs enumerated on leaf counts {ns}; witnesses retained. Finite corpus only."},
        {"id": "endpoint-only-cherry", "label": "Drop side-subtree branch", "status": "refuted" if rules_report["endpoint_rule_status"].startswith("refuted") else "open", "detail": rules_report["endpoint_rule_status"]},
        {"id": "restriction-only-contraction", "label": "Contract any equal restriction", "status": "refuted", "detail": "Conflicting triples: equal two-leaf restriction; deletion reduces optimum from two to one."}
    ]
    update_progress("Exact corpus saved; candidate local rules tested. General correctness remains open.", {"pairs": total_cases, "partitions": tested_partitions, "endpoint_tests": endpoint_tests, "controls": "15/15"}, claims=claims, example=example, status="tested")
    print(json.dumps({"pairs": total_cases, "endpoint_tests": endpoint_tests, "endpoint_rule_status": rules_report["endpoint_rule_status"], "counterexamples": len(counterexamples)}))
    return report


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("controls")
    c = sub.add_parser("corpus")
    c.add_argument("--n", type=int, nargs="+", default=[3, 4])
    s = sub.add_parser("solve")
    s.add_argument("input", type=Path)
    s.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.command == "controls": controls()
    elif args.command == "corpus": corpus(args.n)
    else:
        raw = json.loads(args.input.read_text())
        a, b = pair(raw["a"], raw["b"])
        if "forest" in raw:
            result = validate(a, b, raw["forest"])
        else:
            result = optimum(a, b, all_optima=True)
            result["witness"] = validate(a, b, [list(block) for block in result["forests"][0]])
        result.update(convention=CONVENTION, status="executed-exact-not-Lean")
        if args.output: write_json(args.output, result)
        print(json.dumps(result, indent=2))


if __name__ == "__main__": main()
