#!/usr/bin/env python3
"""One-shot supplemental frozen original-address, boundary and callback controls."""
import collections
import importlib.util
import itertools
import json
import pathlib
import time

HERE = pathlib.Path(__file__).resolve().parent
loader = importlib.util.spec_from_file_location("own_v2", HERE / "instrument-v2.py")
m = importlib.util.module_from_spec(loader)
loader.loader.exec_module(m)


def prune(tree, labels):
    # Literal target/source extraction only, independent graph agreement still
    # uses path hulls and induced clades in the main instrument.
    if isinstance(tree, int):
        return tree if tree in labels else None
    a, b = (prune(t, labels) for t in tree)
    return b if a is None else (a if b is None else [a, b])


def local_minimum(target, sources):
    t = m.Original(target)
    ss = [m.Original(x) for x in sources]
    parents = [s.order for s in ss]
    accepted = []
    for f in m.refiners(parents):
        if not t.disjoint(f):
            continue
        if all(s.disjoint([b for b in f if set(b) <= set(s.order)]) and all(
                s.restriction_equal(t, b) for b in f if set(b) <= set(s.order)) for s in ss):
            accepted.append(f)
    return min(map(len, accepted)) - len(ss), accepted


def main():
    start = time.perf_counter()
    records = []
    root = m.CASES["ROOT8"]
    s, t = m.Original(root["s"]), m.Original(root["t"])
    expected_s = {0:"000", 1:"01", 2:"001", 3:"1000", 4:"101", 5:"1001", 6:"110", 7:"111"}
    expected_t = {0:"00000", 1:"0001", 2:"010", 3:"00001", 4:"001", 5:"011", 6:"10", 7:"11"}
    assert s.leaf == expected_s and t.leaf == expected_t
    expected_hulls = [["0","00","000","0000","00000","0001","01","010"],
                      ["0","00","000","0000","00001","001","01","011"], ["1","10","11"]]
    assert [sorted(t.hull(b)) for b in root["p"]] == [sorted(x) for x in expected_hulls]
    records.append({"root_exact_addresses_hulls": True, "selector": t.selector(*root["p"][:2])})
    base = m.CASES["S8"]
    s, t = m.Original(base["s"]), m.Original(base["t"])
    for name, p in [("C-empty", [base["p"][0],base["p"][1],[]]),
                    ("C-absent", [base["p"][0],base["p"][1],[99]]),
                    ("C-overlap", [base["p"][0],base["p"][1],[1,6,7]])]:
        assert not m.partition(s.order, p)
        records.append({"domain": name, "checked_partition": False,
                        "runtime_refusal_inferred": False})
    # Clear C is an independent theorem hypothesis; a proper source partition
    # alone does not establish it. Put the C cherry into the A/B hull interior.
    overlap_t = m.Original([[[2, [[0,1],[3,[6,7]]]], [4,5]], 99])
    # This is a source-label mismatch boundary, not a false in-regime example.
    assert collections.Counter(overlap_t.order) != collections.Counter(s.order)
    records.append({"boundary": "label-mismatch", "in_regime": False})
    overlap_proper = m.Original([[2, [[[0,6],1],[3,7]]], [4,5]])
    assert collections.Counter(overlap_proper.order) == collections.Counter(s.order)
    assert m.partition(s.order, base["p"]) and s.disjoint(base["p"])
    assert overlap_proper.selector(*base["p"][:2]) == ["edge","0","01"]
    assert not s.restriction_equal(overlap_proper, base["p"][0])
    assert not s.restriction_equal(overlap_proper, base["p"][1])
    assert s.restriction_equal(overlap_proper, base["p"][2])
    c_hull = overlap_proper.hull(base["p"][2])
    assert all(c_hull & overlap_proper.hull(b) for b in base["p"][:2])
    records.append({"boundary":"isolated-C-clearance", "source_proper":True,
                    "selector":["edge","0","01"], "C_clearance":False,
                    "runtime_refusal_inferred":False})
    # Literal selected S11 callback source forests from original source restriction.
    x = m.CASES["S11"]
    bset = set(x["p"][1])
    tb = prune(x["t"], bset)
    sb = prune(x["s"], bset)
    table = json.loads((HERE / "CALLBACK-TABLES-v1.json").read_text())["S11"]
    assert tb == table["T_B"] and sb == table["B_whole"]
    source = m.Original(x["s"])
    target = m.Original(x["t"])
    outside = target.sectors(x["p"][1], "001")[0]
    outs = m.source_core(source, m.tagged(x["p"], 1, outside), 4)["outputs"]
    forests = [[prune(x["s"], set(b)) for b in out["partition"] if set(b) <= bset] for out in outs]
    assert forests == [table["B_forest_opposite0"], table["B_forest_opposite1"]]
    minima, accepted = [], []
    for forest in [[sb]] + forests:
        minimum, fs = local_minimum(tb, forest)
        minima.append(minimum); accepted.append(fs)
    assert minima == table["minimum_additional"]
    calls = []
    for q in [4,5,6]:
        charged = [3,5,5]
        budgets = [q-d for d in charged if d <= q]
        ref = table[f"q{q}"]
        assert budgets == ref["budgets"]
        verdicts = [b >= minima[i] for i,b in enumerate(budgets)]
        if q in [4,5]: assert not any(verdicts)
        for i, answer in enumerate(ref["exact_callbacks"]):
            if answer is not None:
                assert answer in accepted[i]
                assert len(answer) - len(([sb]+[]) if i == 0 else forests[i-1]) <= budgets[i]
        calls.append({"q": q, "budgets": budgets, "exact_successes": verdicts})
    # Actual original returned-length selection on a known feasible candidate.
    whole_s, whole_t = m.Original(x["s"]), m.Original(x["t"])
    best = [[0,1],[2],[3,4],[5],[6],[7,8],[9,10]]
    allsingle = [[a] for a in whole_s.order]
    invalid = x["p"]
    assert m.agreement(whole_s, whole_t, best) and len(best) == 7
    assert not m.agreement(whole_s, whole_t, invalid)
    candidates = [allsingle, invalid, best, allsingle, best]
    valid = [f for f in candidates if m.agreement(whole_s, whole_t, f) and len(f)-1 <= 10]
    assert min(map(len, valid)) == 7
    # Empty/failure/duplicates/early failure reference scheduler, preserving calls.
    def simulate(requests, answers, stop):
        trace = []
        for r,a in zip(requests,answers):
            trace.append(r)
            if a is None and stop: return trace,None
        return trace,answers
    abstract = json.loads((HERE / "CALLBACK-TABLES-v1.json").read_text())["abstract"]
    for name in ["empty","failed","duplicate","early_failure"]:
        row = abstract[name]
        observed,_ = simulate(row["requested"],row["answers"],name=="early_failure")
        assert observed == row["called"]
    # Negative integer labels are representational controls outside formal Nat type.
    def rename(tree):
        return -tree-11 if isinstance(tree,int) else [rename(c) for c in tree]
    rs, rt = m.Original(rename(base["s"])), m.Original(rename(base["t"]))
    rp = [[-a-11 for a in b] for b in base["p"]]
    assert rt.selector(*rp[:2]) == ["edge","00","001"]
    records.append({"negative_integer_representation": "PASS", "formal_Nat_domain": False})
    result = {"status":"PASS", "records":records, "callback_minima":minima, "calls":calls,
              "minimum_returned_blocks":7, "abstract_scheduler_denominator":4,
              "seconds":time.perf_counter()-start,
              "scope":"Frozen finite reference checks; candidate control/trace review awaits RELEASE"}
    m.dump(HERE / "supplemental-v2.json",result)
    print(json.dumps(result))


if __name__ == "__main__": main()
