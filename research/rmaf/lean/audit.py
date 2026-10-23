#!/usr/bin/env python3
"""Replay formal build, per-theorem axioms, and a required negative control.

Scope: executable assignment/embedding model; NOT complete graph-theoretic
rooted-MAF semantic correspondence and NOT an improved exponential algorithm.
Run from any working directory with ./bootloops-python research/rmaf/lean/audit.py.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
OUT = HERE / "audit"
OUT.mkdir(exist_ok=True)


def run(name, args):
    started = time.monotonic()
    proc = subprocess.run(args, cwd=HERE, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True)
    (OUT / f"{name}.log").write_text(proc.stdout)
    return {"exit_code": proc.returncode,
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "log": f"research/rmaf/lean/audit/{name}.log"}, proc.stdout


build, _ = run("build", [str(ROOT / "bootloops-lake"), "build"])
axioms, text = run("axioms", [str(ROOT / "bootloops-lake"), "env", "lean", "RMAF.lean"])
negative, negative_text = run("negative-control", [str(ROOT / "bootloops-lake"), "env", "lean",
                                                   "negative/FalseControl.lean"])
theorems = []
for line in text.splitlines():
    hit = re.search(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", line)
    if hit:
        dependencies = [x.strip() for x in (hit.group(2) or "").split(",") if x.strip()]
        theorems.append({"id": hit.group(1), "axioms": dependencies,
                         "allowed_only": set(dependencies) <= ALLOWED})
source = (HERE / "RMAF.lean").read_text()
source_safe = not re.search(r"\b(?:sorry|admit|native_decide|axiom)\b", source)
expected_theorems = {"RMAF." + name for name in re.findall(r"#print axioms (\S+)", source)}
audit_complete = {t["id"] for t in theorems} == expected_theorems
negative_caught = (negative["exit_code"] != 0 and "error:" in negative_text and
                   "Tactic `decide` proved that the proposition" in negative_text and
                   "is false" in negative_text)
passed = (build["exit_code"] == 0 and axioms["exit_code"] == 0 and
          len(theorems) >= 21 and audit_complete and all(t["allowed_only"] for t in theorems) and
          source_safe and negative_caught)
certificate = {
    "schema_version": 1, "status": "passed" if passed else "failed",
    "scope": "Formal executable assignment/embedding model and finite counterexample; semantic correspondence is open.",
    "no_improved_algorithm_claimed": True,
    "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
    "build": build, "axiom_audit": axioms, "negative_control": negative,
    "negative_control_caught": negative_caught, "source_safe": source_safe,
    "all_declared_audits_present": audit_complete,
    "allowed_axioms": sorted(ALLOWED), "theorems": theorems,
    "remaining_obligations": [
        "Correspondence of inductive RootedIso to graph-labelled root isomorphism; Boolean equivalence is already proved",
        "Minimal graph embedding semantics of minimalVertices",
        "Every set partition is represented by a bounded assignment",
        "Any new reductions and branches preserve/exhaust optimal forests",
        "Worst-case recurrence and original-k exponential bound",
        "Fresh semantic and independent verification"
    ]
}
(OUT / "certificate.json").write_text(json.dumps(certificate, indent=2) + "\n")
print(json.dumps({"status": certificate["status"], "checked_theorems": len(theorems),
                  "negative_control_caught": negative_caught,
                  "certificate": "research/rmaf/lean/audit/certificate.json"}))
raise SystemExit(0 if passed else 1)
