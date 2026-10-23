#!/usr/bin/env python3
"""One-shot original prerelease graph/core controls, deliberately not toolkit code.

Public definitions: PUBLIC-DEFINITIONS-v1.json. No candidate imports or reads.
Agreement uses original adjacency paths plus induced clade sets, not the public
recursive Boolean implementation. Source core is rebuilt from surviving leaves
at every prefix; original LCAs carry origins through contraction.
"""
from __future__ import annotations

import argparse
import collections
import copy
import fractions
import hashlib
import itertools
import json
import pathlib
import time
from typing import Any

HERE = pathlib.Path(__file__).resolve().parent


def dump(path, obj):
    pathlib.Path(path).write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")


class Original:
    def __init__(self, tree):
        self.tree = tree
        self.adj = {}
        self.leaf = {}
        self.order = []
        self.desc = {}
        self.kids = {}
        self.vertices = []
        self.edges = []

        def walk(t, p):
            self.vertices.append(p)
            self.adj.setdefault(p, [])
            if isinstance(t, int):
                if t in self.leaf:
                    raise ValueError("duplicate original leaf")
                self.leaf[t] = p
                self.order.append(t)
                self.desc[p] = frozenset([t])
            else:
                if len(t) != 2:
                    raise ValueError("nonbinary original tree")
                self.kids[p] = (p + "0", p + "1")
                # Public edge ordering lists both root edges before descendant edges.
                self.edges.extend([(p, p + "0"), (p, p + "1")])
                for bit, sub in zip("01", t):
                    self.adj[p].append(p + bit)
                    self.adj.setdefault(p + bit, []).append(p)
                    walk(sub, p + bit)
                self.desc[p] = self.desc[p + "0"] | self.desc[p + "1"]

        walk(tree, "")
        # The adjacency construction appends child edges before recursive subtrees,
        # matching the exposed public ordered edges definition at every vertex.

    def path(self, a, b):
        todo = collections.deque([a])
        prev = {a: None}
        while todo:
            p = todo.popleft()
            if p == b:
                break
            for r in self.adj[p]:
                if r not in prev:
                    prev[r] = p
                    todo.append(r)
        out = set()
        p = b
        while p is not None:
            out.add(p)
            p = prev[p]
        return out

    def hull(self, labels):
        if not labels:
            return set()
        if any(x not in self.leaf for x in labels):
            raise ValueError("hull label absent")
        first = self.leaf[labels[0]]
        result = {first}
        for x in labels[1:]:
            result |= self.path(first, self.leaf[x])
        return result

    def clades(self, labels):
        selected = frozenset(labels)
        if not selected or not selected <= self.desc[""]:
            return None
        return frozenset(frozenset(xs & selected) for xs in self.desc.values()
                         if len(xs & selected) >= 2)

    def restriction_equal(self, other, labels):
        return self.clades(labels) is not None and self.clades(labels) == other.clades(labels)

    def disjoint(self, parts):
        seen = set()
        for b in parts:
            h = self.hull(b)
            if seen & h:
                return False
            seen |= h
        return True

    def region(self, vertex, label):
        p = self.leaf[label]
        if p == vertex:
            return 3
        if p.startswith(vertex):
            return int(p[len(vertex)])
        return 2

    def sectors(self, block, child):
        return ([x for x in block if self.leaf[x].startswith(child)],
                [x for x in block if not self.leaf[x].startswith(child)])

    def selector(self, a, b):
        if (not a or not b or len(set(a)) != len(a) or len(set(b)) != len(b)
                or set(a) & set(b) or not set(a + b) <= set(self.order)):
            return None
        ha, hb = self.hull(a), self.hull(b)
        for v in self.vertices:
            if v in ha & hb and (len({self.region(v, x) for x in a}) == 3 or
                                  len({self.region(v, x) for x in b}) == 3):
                return ["vertex", v]
        for u, v in self.edges:
            if not {u, v} <= ha & hb:
                continue
            aa, bb = self.sectors(a, v), self.sectors(b, v)
            if all(aa) and all(bb) and all(not self.hull(x) & hb for x in aa) and all(
                    not self.hull(x) & ha for x in bb):
                return ["edge", u, v]
        return None


def partition(labels, parts):
    flat = [x for b in parts for x in b]
    return all(parts) and collections.Counter(flat) == collections.Counter(labels)


def agreement(s, t, parts):
    return (partition(s.order, parts) and partition(t.order, parts)
            and all(s.restriction_equal(t, b) for b in parts)
            and s.disjoint(parts) and t.disjoint(parts))


def refines(fine, coarse):
    return all(any(set(b) <= set(c) for c in coarse) for b in fine)


def partitions(labels):
    if not labels:
        yield []
        return
    first, *rest = labels
    for p in partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


def refiners(parents):
    for pieces in itertools.product(*(list(partitions(p)) for p in parents)):
        yield [b for pp in pieces for b in pp]


def common_prefix(paths):
    p = paths[0]
    for q in paths[1:]:
        p = p[:next((i for i in range(min(len(p), len(q))) if p[i] != q[i]), min(len(p), len(q)))]
    return p


def source_core(source, colors, budget):
    """Recompute surviving-leaf clades, contract color-uniform clades, then branch.

    No public implementation is copied. Prefix counters include failed/pruned
    child attempts. Output blocks/cuts preserve original literal order.
    """
    rec = {"outputs": [], "refusals": [], "visited": 0, "attempts": 0, "pruned": 0}

    def compressed(xs):
        p = common_prefix([source.leaf[x] for x in xs])
        if len({colors[x] for x in xs}) == 1:
            return {"origin": p, "labels": xs, "color": colors[xs[0]]}
        left = [x for x in xs if source.leaf[x].startswith(p + "0")]
        right = [x for x in xs if source.leaf[x].startswith(p + "1")]
        assert left and right
        return [compressed(left), compressed(right)]

    def tips(tree):
        if isinstance(tree, dict):
            return [tree]
        return tips(tree[0]) + tips(tree[1])

    def first_cherry(tree):
        if isinstance(tree, dict):
            return None
        if all(isinstance(x, dict) for x in tree):
            return tree
        return first_cherry(tree[0]) or first_cherry(tree[1])

    def run(xs, detached, cuts, remaining):
        rec["visited"] += 1
        tree = compressed(xs)
        gs = tips(tree)
        if len({g["color"] for g in gs}) == 1:
            rec["outputs"].append({"partition": detached + [xs], "cuts": cuts})
            return
        count = collections.Counter(g["color"] for g in gs)
        single = next((g for g in gs if count[g["color"]] == 1), None)
        choices = [single] if single else first_cherry(tree)
        assert choices
        for g in choices:
            rec["attempts"] += 1
            if not g["origin"]:
                rec["refusals"].append("original root")
            elif g["origin"] in cuts:
                rec["refusals"].append("duplicate cut")
            elif remaining == 0:
                rec["pruned"] += 1
            else:
                gone = set(g["labels"])
                new = [x for x in xs if x not in gone]
                assert new
                run(new, [g["labels"]] + detached, [g["origin"]] + cuts, remaining - 1)

    run(source.order, [], [], min(budget, len(source.order) - 1))
    return rec


def tagged(parents, split_parent, sector):
    result = {}
    for idx, p in enumerate(parents):
        for x in p:
            result[x] = idx + (3 if idx == split_parent and x not in sector else 0)
    return result


CASES = {
    "ROOT8": {"s": [[[0, 2], 1], [[[3, 5], 4], [6, 7]]],
              "t": [[[[[0, 3], 1], 4], [2, 5]], [6, 7]],
              "p": [[0, 1, 2], [3, 4, 5], [6, 7]], "selector": ["vertex", "00"]},
    "S8": {"s": [[[0, 2], 1], [[[3, 5], 4], [6, 7]]],
           "t": [[[2, [[0, 1], 3]], [4, 5]], [6, 7]],
           "p": [[0, 1, 2], [3, 4, 5], [6, 7]], "selector": ["edge", "00", "001"]},
    "S9": {"s": [[[[0, 2], 1], 3], [[[4, 6], 5], [7, 8]]],
           "t": [[[3, [[[0, 1], 2], 4]], [5, 6]], [7, 8]],
           "p": [[0, 1, 2, 3], [4, 5, 6], [7, 8]], "selector": ["edge", "00", "001"]},
    "S10": {"s": [[[0, 2], [1, 3]], [[[4, 6], [5, 7]], [8, 9]]],
            "t": [[[[2, 3], [[0, 1], [4, 5]]], [6, 7]], [8, 9]],
            "p": [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9]], "selector": ["edge", "00", "001"]},
}


def assert_equal(got, expected, name):
    if got != expected:
        raise AssertionError(json.dumps({"check": name, "got": got, "expected": expected}, sort_keys=True))


def plants():
    records = []
    identical = Original([[10, 20], [30, 40]])
    different = Original([[10, 30], [20, 40]])
    for name, t, f, expected in [
        ("whole-identical", identical, [[10, 20, 30, 40]], True),
        ("singletons-identical", identical, [[10], [20], [30], [40]], True),
        ("split-identical", identical, [[10, 20], [30, 40]], True),
        ("whole-corrupt-shape", different, [[10, 20, 30, 40]], False),
        ("target-overlap", different, [[10, 20], [30, 40]], False),
        ("different-singletons", different, [[10], [20], [30], [40]], True),
        ("empty-block", identical, [[], [10, 20, 30, 40]], False),
        ("duplicated-label", identical, [[10, 10], [20], [30], [40]], False),
        ("absent-label", identical, [[10], [20], [30], [99]], False),
        ("incomplete", identical, [[10], [20], [30]], False),
    ]:
        got = agreement(identical, t, f)
        assert_equal(got, expected, name)
        records.append({"name": name, "observed": got, "expected": expected})
    assert_equal(identical.hull([10, 20]), {"0", "00", "01"}, "hull-plant")
    # Comparator's own wrong-answer plant must trip, and clean twin pass.
    caught = False
    try:
        assert_equal(True, False, "deliberate-comparator-mismatch")
    except AssertionError:
        caught = True
    assert caught
    return {"plants": records, "denominator": 10, "comparator_mismatch_caught": caught}


def arithmetic():
    F = fractions.Fraction
    rows = []
    for c in [F(2), F(233, 100), F(3), F(4)]:
        bound = 4 / c**4
        raw = sum((c**(-d) for d in [3, 4, 4]), F())
        charged = sum((c**(-d) for d in [3, 5, 5]), F())
        assert_equal(raw <= bound, c == 2, f"raw-{c}")
        assert_equal(charged <= bound, c <= 3, f"charged-{c}")
        rows.append({"c": str(c), "in_domain": 2 <= c <= 3, "raw": str(raw),
                     "charged": str(charged), "bound": str(bound),
                     "raw_ok": raw <= bound, "charged_ok": charged <= bound})
    budgets = lambda q: [q - d for d in [3, 5, 5] if d <= q]
    assert_equal(budgets(5), [2, 0, 0], "q5")
    assert_equal(budgets(4), [1], "q4")
    assert_equal(budgets(2), [], "q2")
    return rows


def case_control(name, spec, enumerate_all=True):
    start = time.perf_counter()
    s, t, p = Original(spec["s"]), Original(spec["t"]), spec["p"]
    choice = t.selector(*p[:2])
    assert_equal(choice, spec["selector"], name + ":selector")
    assert partition(s.order, p) and s.disjoint(p)
    assert not s.restriction_equal(t, p[0]) and not s.restriction_equal(t, p[1])
    assert s.restriction_equal(t, p[2])
    assert not t.hull(p[2]) & (t.hull(p[0]) | t.hull(p[1]))
    result = {"name": name, "selector": choice, "source_leaves": s.leaf,
              "target_leaves": t.leaf, "source_hulls": [sorted(s.hull(b)) for b in p],
              "target_hulls": [sorted(t.hull(b)) for b in p], "cores": {}}
    fs = []
    denominator = 0
    if enumerate_all:
        for f in refiners(p):
            denominator += 1
            if agreement(s, t, f):
                fs.append(f)
        result["refiner_denominator"] = denominator
        result["AFs"] = fs
        result["minimum_blocks"] = min(map(len, fs))
    if choice[0] == "edge":
        child = choice[2]
        result["sector_good"] = []
        for idx in [0, 1]:
            sectors = t.sectors(p[idx], child)
            result["sector_good"].append([s.restriction_equal(t, b) for b in sectors])
            colors = tagged(p, idx, sectors[0])
            for q in [3, 4, 5]:
                rec = source_core(s, colors, q)
                for out in rec["outputs"]:
                    assert partition(s.order, out["partition"])
                    assert s.disjoint(out["partition"])
                    assert len(out["cuts"]) == len(out["partition"]) - 1
                    assert len(out["cuts"]) <= q
                result["cores"][f"split{'AB'[idx]}-q{q}"] = rec
        if enumerate_all:
            covered = []
            for f in fs:
                # At sufficient q every original AF is covered by at least one
                # literal source core. Two-side ownership is checked separately.
                crossing = [any(any(t.leaf[x].startswith(child) for x in b) and
                                any(not t.leaf[x].startswith(child) for x in b)
                                for b in f if set(b) <= set(p[idx])) for idx in [0, 1]]
                assert not all(crossing)
                owners = []
                for idx in [0, 1]:
                    outs = result["cores"][f"split{'AB'[idx]}-q5"]["outputs"]
                    if any(refines(f, out["partition"]) for out in outs):
                        owners.append(idx)
                assert owners
                covered.append({"F": f, "crossing": crossing, "cover_cores": owners})
            result["coverage"] = covered
    if name == "ROOT8":
        assert_equal(result["minimum_blocks"], 5, "root minimum")
        assert agreement(s, t, [[0, 1], [2], [3], [4, 5], [6, 7]])
    if name == "S8":
        assert_equal(result["minimum_blocks"], 5, "S8 minimum")
        exp = json.loads((HERE / "CORE-EXPECTATIONS-v1.json").read_text())
        for idx in "AB":
            assert_equal(result["cores"][f"split{idx}-q3"]["outputs"],
                         exp[f"S8_split{idx}"]["outputs"], f"S8 split{idx} exact")
        for f in [[[0, 2], [1], [3], [4, 5], [6, 7]],
                  [[0, 1], [2], [3, 5], [4], [6, 7]]]:
            assert agreement(s, t, f)
        both = [[0, 2], [1], [3, 5], [4], [6, 7]]
        assert s.disjoint(both) and not t.disjoint(both) and not agreement(s, t, both)
    if name == "S9":
        assert_equal(result["sector_good"], [[False, True], [True, True]], "S9 sectors")
        for idx in "AB":
            assert_equal(len(result["cores"][f"split{idx}-q3"]["outputs"]), 1, "S9 cheap probe")
    if name == "S10":
        for idx in "AB":
            assert_equal(result["cores"][f"split{idx}-q3"]["outputs"], [], "S10 failed probe")
    result["seconds"] = time.perf_counter() - start
    return result


def ledger_plants():
    clean = {
        "coverage_occurrences": ["a", "b", "b"], "mass_occurrences": ["a", "b", "b"],
        "expected_calls": [["T", ["A0", "A1", "B", "C"], 2], ["TB", ["B0", "B1"], 0]],
        "actual_calls": [["T", ["A0", "A1", "B", "C"], 2], ["TB", ["B0", "B1"], 0]],
        "q": 5, "fixed_parent": 2, "d": 3, "paid": 1, "retained_budget": 1,
        "pruned_before_subtract": True, "selector_checked": True, "clearance_checked": True,
        "runtime_dependencies": ["S", "T", "P", "q"],
        "required_premises": ["original_refinement", "everyF_paid_lower", "cross_group_source"],
        "work_expected": ["prefix", "refusal", "append", "materialize", "checker", "payload"],
        "work_charged": ["prefix", "refusal", "append", "materialize", "checker", "payload"],
    }

    def failures(v):
        fail = []
        for field in ["selector_checked", "clearance_checked", "pruned_before_subtract"]:
            if not v[field]: fail.append(field)
        if v["coverage_occurrences"] != v["mass_occurrences"]: fail.append("same_occurrences")
        if v["expected_calls"] != v["actual_calls"]: fail.append("literal_calls")
        if v["retained_budget"] != v["q"] - v["d"] - v["paid"]: fail.append("retained_budget")
        if v["fixed_parent"] != 2: fail.append("fixed_parent_once")
        if not set(v["runtime_dependencies"]) <= {"S", "T", "P", "q"}: fail.append("runtime_dependency")
        if v["required_premises"] != clean["required_premises"]: fail.append("premises")
        if v["work_charged"] != v["work_expected"]: fail.append("work_components")
        return fail

    mutations = []
    def add(name, fn, detector):
        v = copy.deepcopy(clean); fn(v)
        got = failures(v)
        assert detector in got, (name, got)
        mutations.append({"name": name, "detector": detector, "caught": got})
    assert failures(clean) == []
    add("missing-selector", lambda v: v.update(selector_checked=False), "selector_checked")
    add("missing-clearance", lambda v: v.update(clearance_checked=False), "clearance_checked")
    for name, vals in [("drop-cover", ["a", "b"]), ("duplicate-charge", ["a", "b", "b", "b"]),
                       ("omit-charge", ["a"]), ("favorable-filter", ["a", "b"])]:
        add(name, lambda v, xs=vals: v.update(mass_occurrences=xs), "same_occurrences")
    for name, vals in [("wrong-target", [["wrong", ["A0", "A1", "B", "C"], 2]]),
                       ("wrong-source", [["T", ["A"], 2]]),
                       ("free-whole-B", [["TB", ["original_whole_B"], 0]]),
                       ("omit-call", []), ("duplicate-call", clean["actual_calls"] * 2)]:
        add(name, lambda v, xs=vals: v.update(actual_calls=xs), "literal_calls")
    add("q-versus-additional", lambda v: v.update(retained_budget=3), "retained_budget")
    add("double-parent", lambda v: v.update(fixed_parent=4), "fixed_parent_once")
    add("subtract-before-prune", lambda v: v.update(pruned_before_subtract=False), "pruned_before_subtract")
    add("local-to-whole-union", lambda v: v.update(required_premises=["invented_cut_union"]), "premises")
    add("own-minimum-free", lambda v: v.update(required_premises=["own_minimum_positive"]), "premises")
    add("hidden-optimum", lambda v: v.update(runtime_dependencies=["S", "T", "Fopt"]), "runtime_dependency")
    for comp in clean["work_expected"]:
        add("uncharged-" + comp, lambda v, c=comp: v.update(work_charged=[x for x in v["work_charged"] if x != c]), "work_components")
    return {"clean_twin_pass": True, "denominator": len(mutations), "mutations": mutations,
            "scope": "semantic ledger controls only; actual source adapters pending RELEASE"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["plants", "pilot1", "pilot4", "bank"])
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    started = time.time()
    out = {"mode": args.mode, "started_unix": started,
           "instrument_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
    if args.mode == "plants":
        out["truth"] = plants()
        out["arithmetic"] = arithmetic()
        out["ledger"] = ledger_plants()
    else:
        cases = ["ROOT8"] if args.mode == "pilot1" else list(CASES)
        out["cases"] = []
        dump(args.output, out)
        for name in cases:
            row = case_control(name, CASES[name])
            out["cases"].append(row)
            dump(args.output, out)
            print(json.dumps({"completed": name, "seconds": row["seconds"],
                              "refiners": row.get("refiner_denominator"),
                              "minimum_blocks": row.get("minimum_blocks")}))
    out["elapsed_seconds"] = time.time() - started
    out["status"] = "PASS"
    dump(args.output, out)
    print(json.dumps({"mode": args.mode, "status": "PASS", "elapsed_seconds": out["elapsed_seconds"]}))


if __name__ == "__main__":
    main()
