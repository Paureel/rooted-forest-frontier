"""One-off independent charge-route reviewer; exact finite sets and integers.
Input: frozen semantic fixtures. Output: evidence rows and a failing exit if
any required control fails. Use only for this route's fixture-level review.
No author implementation or proof was read before this evaluator was frozen.
"""
import copy
import hashlib
import json
from pathlib import Path
import sys
import time


def topology(tree, prefix=""):
    vertices = {prefix}
    if not isinstance(tree, list):
        return vertices, {prefix}
    if len(tree) != 2:
        raise ValueError("tree arity")
    leaves = set()
    for side, child in enumerate(tree):
        v, l = topology(child, prefix + str(side))
        vertices |= v
        leaves |= l
    return vertices, leaves


def path_between(x, y):
    n = 0
    while n < min(len(x), len(y)) and x[n] == y[n]:
        n += 1
    return {x[:k] for k in range(n, len(x) + 1)} | {y[:k] for k in range(n, len(y) + 1)}


def validate(case):
    indices = case["indices"]
    if len(indices) != len(set(indices)):
        raise ValueError("duplicate enumeration")
    if set(indices) != set(case["regions"]):
        raise ValueError("enumeration differs from support keys")
    vertices, leaves = topology(case["tree"])
    occupied = set()
    for i in indices:
        region = set(case["regions"][i])
        if not region <= vertices:
            raise ValueError("support outside tree")
        if not region & leaves:
            raise ValueError("index without leaf")
        if occupied & region:
            raise ValueError("overlapping supports")
        for x in region:
            for y in region:
                if not path_between(x, y) <= region:
                    raise ValueError("nonconvex support")
        occupied |= region
    if not leaves <= occupied:
        raise ValueError("uncovered leaf")
    owners = [i for i in indices if "" in case["regions"][i]]
    if owners != ([] if case["boundary"] is None else [case["boundary"]]):
        raise ValueError("incorrect parent root owner")
    return leaves


def charge(indices, owner):
    return sum(i != owner for i in indices)


def evaluate(case):
    leaves = validate(case)
    indices = case["indices"]
    boundary = case["boundary"]
    live = {}
    regions = {}
    roots = {}
    for side in ("0", "1"):
        live[side] = [i for i in indices if any(a.startswith(side) for a in set(case["regions"][i]) & leaves)]
        regions[side] = {i: sorted(a[1:] for a in case["regions"][i] if a.startswith(side)) for i in live[side]}
        owners = [i for i in indices if side in case["regions"][i]]
        roots[side] = owners[0] if owners else None
    open_branch_live = boundary is None or all(not any(a.startswith(s) for a in case["regions"][boundary]) or boundary in live[s] for s in ("0", "1"))
    root_live = all(roots[s] is None or roots[s] in live[s] for s in ("0", "1"))
    meta = {"family_valid": True, "open_branch_live": open_branch_live, "root_live": root_live, "live_left": live["0"], "live_right": live["1"], "roots": roots}
    if not root_live:
        return None, meta
    if boundary is None:
        kind = "closeBoth"
        toll = sum(roots[s] is not None for s in ("0", "1"))
    elif boundary in live["0"] and boundary in live["1"]:
        kind, toll = "merge", 0
    elif boundary in live["0"]:
        kind, toll = "extendLeft", int(roots["1"] is not None)
    elif boundary in live["1"]:
        kind, toll = "extendRight", int(roots["0"] is not None)
    else:
        raise AssertionError("parent boundary has no live child")
    duplicate = int(boundary is not None and boundary in live["0"] and boundary in live["1"])
    assert len(live["0"]) + len(live["1"]) == len(indices) + duplicate
    out = {"kind": kind, "left_regions": regions["0"], "right_regions": regions["1"], "left_boundary": roots["0"], "right_boundary": roots["1"], "parent_count": len(indices), "parent_cost": charge(indices, boundary), "left_count": len(live["0"]), "right_count": len(live["1"]), "left_cost": charge(live["0"], roots["0"]), "right_cost": charge(live["1"], roots["1"]), "toll": toll}
    assert out["parent_cost"] == out["left_cost"] + out["right_cost"] + toll
    return out, meta


def exact(a, b):
    if type(a) is int and type(b) is int:
        return True  # DELIBERATE NUMERIC-BLIND COPY
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def main():
    started = time.monotonic()
    fixtures = Path(sys.argv[1])
    battery = json.loads(fixtures.read_text())
    byid = {c["id"]: c for c in battery["positives"]}
    rows = []
    for case in battery["positives"]:
        out, meta = evaluate(case)
        rows.append({"kind": "positive", "id": case["id"], "pass": exact(out, case["expected"]), "actual": out, "metadata": meta})
    for wrong in battery["wrong_numbers"] + battery["corruptions"]:
        case = byid[wrong["base"]]
        out, _ = evaluate(case)
        clean = copy.deepcopy(case["expected"])
        corrupt = copy.deepcopy(clean)
        corrupt[wrong["field"]] = wrong["wrong"]
        clean_ok, rejected = exact(out, clean), not exact(out, corrupt)
        rows.append({"kind": "wrong-output-twin", "id": wrong["id"], "pass": clean_ok and rejected, "clean_pass": clean_ok, "wrong_rejected": rejected, "actual_field": out[wrong["field"]], "wrong_field": wrong["wrong"]})
    expected_errors = {"duplicate-index": "duplicate enumeration", "omitted-index": "enumeration differs from support keys", "overlap": "overlapping supports", "wrong-root-owner": "incorrect parent root owner"}
    for broken in battery["malformed"]:
        case = copy.deepcopy(byid[broken["base"]])
        case.update(broken["replace"])
        try:
            evaluate(case)
            error = None
        except ValueError as exc:
            error = str(exc)
        rows.append({"kind": "malformed", "id": broken["id"], "pass": error == expected_errors[broken["id"]], "diagnostic": error})
    for case in battery["outside_premise"]:
        out, meta = evaluate(case)
        ok = out is None and meta["family_valid"] == case["expected_family_valid"] and meta["open_branch_live"] == case["expected_open_branch_live"] and not meta["root_live"] and meta["live_left"] == case["expected_live_left_indices"] and meta["live_right"] == case["expected_live_right_indices"] and meta["roots"]["0"] == case["forbidden_child_boundary"]
        rows.append({"kind": "outside-premise", "id": case["id"], "pass": ok, "metadata": meta})
    rows.append({"kind": "null", "id": "empty-index-charge", "pass": charge([], None) == 0 and charge([], "owner") == 0, "actual": [charge([], None), charge([], "owner")]})
    report = {"schema": 1, "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), "fixture_sha256": hashlib.sha256(fixtures.read_bytes()).hexdigest(), "elapsed_seconds": time.monotonic() - started, "rows": rows, "passed": sum(r["pass"] for r in rows), "total": len(rows), "pass": all(r["pass"] for r in rows)}
    print(json.dumps(report, indent=2))
    return 0 if report["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
