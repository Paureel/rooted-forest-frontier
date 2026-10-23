"""One-shot 2026-10-14 semantic review: fresh path-hull controls and Lean rebuild.

Run with ./bootloops-python research/rmaf/bridge_review/executable/fresh_review/run_review.py.
No project oracle or checker is imported. Outputs are exact finite comparisons,
dependency hashes, compiler transcripts and measured timings, not global G1 claims.
The frozen hand controls and deliberate corruptions must pass before source builds.
"""
from pathlib import Path
from itertools import product, combinations
from functools import lru_cache
import hashlib
import json
import os
import re
import shutil
import subprocess
import time
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[5]
OWN = Path(__file__).resolve().parent
BUILD = OWN / "build"
LOGS = OWN / "logs" / datetime.now(timezone.utc).strftime("replay-%Y%m%dT%H%M%S%fZ")


def leaf_occurrences(tree, prefix=()):
    if isinstance(tree, int):
        return [(prefix, tree)]
    return leaf_occurrences(tree[0], prefix + (False,)) + leaf_occurrences(tree[1], prefix + (True,))


def hull(tree, selected):
    endpoints = [p for p, label in leaf_occurrences(tree) if label in selected]
    if not endpoints:
        return []
    common = list(endpoints[0])
    for p in endpoints[1:]:
        while tuple(common) != p[:len(common)]:
            common.pop()
    return sorted({p[:n] for p in endpoints for n in range(len(common), len(p) + 1)})


def connected(vertices):
    remaining = set(vertices)
    if not remaining:
        return True
    stack = [remaining.pop()]
    while stack:
        current = stack.pop()
        neighbors = {current + (False,), current + (True,)}
        if current:
            neighbors.add(current[:-1])
        found = neighbors & remaining
        remaining -= found
        stack.extend(found)
    return not remaining


def exact_equal(actual, expected):
    return actual == expected


def lean_path(p):
    return "[" + ",".join("true" if b else "false" for b in p) + "]"


def lean_support(support):
    return "[" + ",".join(lean_path(p) for p in support) + "]"


def lean_tree(tree):
    if isinstance(tree, int):
        return f"(.leaf {tree})"
    return f"(.node {lean_tree(tree[0])} {lean_tree(tree[1])})"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_lean(name, source, emit=False):
    cmd = [str(ROOT / "bootloops-lean")]
    if emit:
        cmd.extend(["-o", str(BUILD / (source.stem + ".olean"))])
    cmd.append(str(source))
    env = dict(os.environ)
    env["LEAN_PATH"] = str(BUILD)
    started = time.perf_counter()
    try:
        p = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True, timeout=60)
        result = {"command": cmd, "elapsed_seconds": time.perf_counter() - started,
                  "returncode": p.returncode, "stdout": p.stdout, "stderr": p.stderr}
    except subprocess.TimeoutExpired as e:
        result = {"command": cmd, "elapsed_seconds": time.perf_counter() - started,
                  "timeout": True, "stdout": str(e.stdout), "stderr": str(e.stderr)}
    (LOGS / (name + ".json")).write_text(json.dumps(result, indent=2))
    (LOGS / (name + ".log")).write_text(result["stdout"] + result["stderr"])
    print(json.dumps({"stage": name, "elapsed_seconds": result["elapsed_seconds"],
                      "returncode": result.get("returncode"), "timeout": result.get("timeout", False)}), flush=True)
    return result


def false_proof_rejected(result):
    text = result["stdout"] + result["stderr"]
    return (result.get("returncode") == 1 and not result.get("timeout")
            and re.search(r"Tactic [`']decide[`'] proved that the proposition", text) is not None
            and "is false" in text
            and "minimalVertices [0, 2]" in text
            and "[[], [false, false], [true], [true, false]]" in text
            and text.count("error:") == 1
            and "Unknown identifier" not in text and "unknown identifier" not in text)


@lru_cache(None)
def shapes(n):
    if n == 1:
        return (None,)
    return tuple((left, right) for k in range(1, n)
                 for left in shapes(k) for right in shapes(n-k))


def label_shape(shape, labels):
    if shape is None:
        return next(labels)
    return (label_shape(shape[0], labels), label_shape(shape[1], labels))


def main():
    BUILD.mkdir(exist_ok=True)
    LOGS.mkdir(parents=True, exist_ok=False)
    print(f"Retained replay directory: {LOGS.relative_to(ROOT)}", flush=True)
    quartet = ((0, 1), (2, 3))
    crossing = [(), (False,), (False, False), (True,), (True, False)]
    deleted = [(), (False, False), (True,), (True, False)]
    controls = [
        ("empty", quartet, (), []),
        ("absent", quartet, (9,), []),
        ("singleton", quartet, (1,), [(False, True)]),
        ("branching", quartet, (0, 2), crossing),
        ("one_suppressed", quartet, (0, 1), [(False,), (False, False), (False, True)]),
        ("leaf_present", 7, (7,), [()]),
        ("leaf_absent", 7, (8,), []),
        ("duplicate_labels", ((0, 0), (2, 3)), (0,), [(False,), (False, False), (False, True)]),
        ("two_suppressed", (((0, 1), 2), 3), (0, 1), [(False, False), (False, False, False), (False, False, True)]),
    ]
    control_rows = []
    for name, tree, selected, expected in controls:
        actual = hull(tree, selected)
        assert exact_equal(actual, expected), (name, actual, expected)
        assert connected(actual), name
        mutated = expected + [(True,) * 9]
        assert not exact_equal(actual, mutated), name
        control_rows.append({"name": name, "expected": expected, "actual": actual,
                             "exact": True, "connected": True, "wrong_twin_rejected": True})
    assert connected(crossing)
    assert not connected(deleted)
    assert not exact_equal(crossing, deleted)
    (LOGS / "planted-controls.json").write_text(json.dumps({"controls": control_rows,
        "count": len(control_rows), "deleted_path_disconnected": True,
        "restored_path_connected": True}, indent=2))
    print("PLANTS: 9/9 exact controls; 9/9 wrong twins rejected; deleted path rejected; restored path accepted", flush=True)

    sources = [
        ROOT / "research/rmaf/lean/RMAF.lean",
        ROOT / "research/rmaf/pure_bridge/lean/PureBridge.lean",
        ROOT / "research/rmaf/bridge_review/lean/GraphRegion.lean",
        ROOT / "research/rmaf/bridge_review/executable/lean/ExecutableConnectivity.lean",
        ROOT / "research/rmaf/bridge_review/executable/lean/ExtractorControls.lean",
    ]
    before = {str(p.relative_to(ROOT)): digest(p) for p in sources}
    (LOGS / "source-hashes-before.json").write_text(json.dumps(before, indent=2))
    for src in sources:
        dst = BUILD / src.name
        shutil.copyfile(src, dst)
        r = run_lean("build-" + src.stem, dst, emit=True)
        assert r.get("returncode") == 0, r
        assert not re.search(r"\bsorryAx\b|\bnative_decide\b", r["stdout"] + r["stderr"])

    generated = ["import ExecutableConnectivity", "open RMAF BridgeReview ExecutableBridge",
                 "namespace FreshExecutableReview", "set_option maxRecDepth 10000"]
    for i, (name, tree, selected, expected) in enumerate(controls):
        generated.append(f"theorem hand_{name} : minimalVertices {list(selected)} {lean_tree(tree)} = {lean_support(expected)} := by decide")
    cases = []
    selections = [tuple(c) for size in range(4) for c in combinations((0, 1, 9), size)]
    for n in range(1, 5):
        for shape in shapes(n):
            for labels in product((0, 1), repeat=n):
                tree = label_shape(shape, iter(labels))
                for selected in selections:
                    support = hull(tree, selected)
                    assert connected(support)
                    endpoints = [p for p, label in leaf_occurrences(tree) if label in selected]
                    assert bool(support) == bool(endpoints)
                    assert set(endpoints) <= set(support)
                    i = len(cases)
                    generated.append(f"theorem finite_{i} : minimalVertices {list(selected)} {lean_tree(tree)} = {lean_support(support)} := by decide")
                    cases.append({"tree": tree, "selected": selected, "expected_support": support})
    assert len(cases) == 816
    generated.append("end FreshExecutableReview")
    (BUILD / "FreshControls.lean").write_text("\n".join(generated) + "\n")
    (LOGS / "finite-cases.json").write_text(json.dumps(cases))
    result = run_lean("fresh-controls", BUILD / "FreshControls.lean", emit=True)
    assert result.get("returncode") == 0, result

    false_text = "import RMAF\nopen RMAF\nexample : minimalVertices [0,2] " + lean_tree(quartet) + " = "
    (BUILD / "FalseProof.lean").write_text(false_text + lean_support(deleted) + " := by decide\n")
    (BUILD / "PositiveTwin.lean").write_text(false_text + lean_support(crossing) + " := by decide\n")
    (BUILD / "MalformedNegative.lean").write_text("import RMAF\nexample : (0 : Nat) = 1 := by exact reviewer_nonexistent_name\n")
    positive = run_lean("positive-twin", BUILD / "PositiveTwin.lean")
    false = run_lean("false-proof", BUILD / "FalseProof.lean")
    malformed = run_lean("malformed-negative", BUILD / "MalformedNegative.lean")
    assert positive.get("returncode") == 0
    assert false_proof_rejected(false), false
    assert malformed.get("returncode") != 0
    assert not false_proof_rejected(malformed)
    assert not false_proof_rejected(positive)
    hostile = [dict(false, returncode=0), dict(false, timeout=True),
               dict(false, stdout=false["stdout"] + "\nerror: Unknown identifier x"),
               dict(false, stdout="error: arbitrary failure"),
               dict(false, returncode=None)]
    assert all(not false_proof_rejected(item) for item in hostile)

    shutil.copyfile(OWN / "InterfaceAudit.lean", BUILD / "InterfaceAudit.lean")
    interface = run_lean("interface-audit", BUILD / "InterfaceAudit.lean", emit=True)
    assert interface.get("returncode") == 0, interface
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    axiom_rows = []
    for name in [p.stem for p in sources] + ["InterfaceAudit"]:
        source = (BUILD / (name + ".lean")).read_text()
        clean = re.sub(r"/\-.*?\-/", "", source, flags=re.S)
        clean = re.sub(r"--[^\n]*", "", clean)
        assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", clean)
        stem = "interface-audit" if name == "InterfaceAudit" else "build-" + name
        log = (LOGS / (stem + ".log")).read_text()
        entries = re.findall(r"^'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$", log, re.M)
        assert len(entries) == len(re.findall(r"^#print axioms ", source, re.M))
        for declaration, _, axioms in entries:
            assert {a.strip() for a in axioms.split(",") if a.strip()} <= allowed, declaration
        axiom_rows.append({"module": name, "printed_declarations": len(entries), "standard_axioms_only": True})
    assert re.findall(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", "axiom planted : False") == ["axiom"]
    assert not {"planted"} <= allowed
    (LOGS / "axiom-source-audit.json").write_text(json.dumps({"modules": axiom_rows,
        "total_printed_declarations": sum(r["printed_declarations"] for r in axiom_rows),
        "scanner_and_allowlist_plants_rejected": True}, indent=2))
    after = {str(p.relative_to(ROOT)): digest(p) for p in sources}
    (LOGS / "source-hashes-after.json").write_text(json.dumps(after, indent=2))
    assert before == after
    final = {"hand_controls": 9, "finite_exact_cases": len(cases),
        "independent_BFS_cases": len(cases), "source_hashes_unchanged": before == after,
        "positive_twin_passed": True, "false_proof_rejected_for_expected_reason": True,
        "malformed_control_not_counted": True, "parser_hostile_mutations_rejected": len(hostile),
        "interface_audit_passed": True, "standard_axioms_only": True,
        "axiom_reports": sum(r["printed_declarations"] for r in axiom_rows)}
    (LOGS / "SUMMARY.json").write_text(json.dumps(final, indent=2))
    print(json.dumps(final, indent=2), flush=True)


if __name__ == "__main__":
    main()
