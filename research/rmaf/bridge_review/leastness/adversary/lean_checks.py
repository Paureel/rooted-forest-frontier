#!/usr/bin/env python3
"""One-shot exact unchanged-source Lean checks for this adversary arm.

Generated expected values come from frozen hand fixtures and the separate
edge/subset graph oracle, never from Lean output. Diagnostics are retained.
Run with ./bootloops-python; it invokes ./bootloops-lean for every Lean run.
"""
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import time
from audit import BASE, lean_tree, lean_addresses

ROOT = BASE.parents[4]
LEAN = BASE / "lean"
RECEIPTS = BASE / "receipts"

def run_lean(name, source, output=None):
    import os
    command = [str(ROOT / "bootloops-lean"), "-R", str(source.parent)]
    if output:
        command += ["-o", str(output)]
    command += [str(source)]
    env = dict(os.environ, LEAN_PATH=str(LEAN))
    start = time.perf_counter()
    result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                            capture_output=True, timeout=60)
    elapsed = time.perf_counter() - start
    log = RECEIPTS / f"{name}.log"
    log.write_text(result.stdout + result.stderr)
    return dict(id=name, command=command, returncode=result.returncode,
                seconds=elapsed, log=str(log),
                source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                output_sha256=hashlib.sha256(log.read_bytes()).hexdigest())

def write_checks(name, records):
    lines = ["import RMAF", "namespace LeastnessAdversary", "set_option maxRecDepth 10000"]
    for n, record in enumerate(records):
        lines.append(f"theorem {name}_{n} : RMAF.minimalVertices {record['selection']} {lean_tree(record['tree'])} = {lean_addresses(record['support'])} := by decide")
        lines.append(f"#print axioms {name}_{n}")
    lines += ["end LeastnessAdversary", ""]
    source = LEAN / f"{name}.lean"
    source.write_text("\n".join(lines))
    return source

def main():
    frozen = json.loads((BASE / "controls/frozen.json").read_text())
    fixtures = frozen["cases"]
    corpus = json.loads((BASE / "results/bound4-cases.json").read_text())
    rows = []
    row = run_lean("original-rmaf", ROOT / "research/rmaf/lean/RMAF.lean", LEAN / "RMAF.olean")
    rows.append(row)
    assert row["returncode"] == 0, row
    for name, records in (("FrozenFixtures", fixtures), ("GraphCorpus", corpus)):
        row = run_lean(name, write_checks(name, records))
        row["expected_theorem_count"] = len(records)
        rows.append(row)
        assert row["returncode"] == 0, row
        text = Path(row["log"]).read_text()
        assert text.count("does not depend on any axioms") == len(records), row
    q = lean_tree([[1,2],[3,4]])
    failures = {
        "SemanticMissingTerminal": f"example : [false, false] ∉ RMAF.minimalVertices [1,2] {q} := by decide\n",
        "SemanticExtraRoot": f"example : RMAF.minimalVertices [1,2] {q} = [[], [false], [false,false], [false,true]] := by decide\n",
        "MalformedProof": f"example : RMAF.minimalVertices [1,2] {q} = [[false], [false,false], [false,true]] := by exact True.intro\n",
    }
    for name, assertion in failures.items():
        source = LEAN / f"{name}.lean"
        source.write_text("import RMAF\n" + assertion)
        row = run_lean(name, source)
        row["expected_failure"] = True
        rows.append(row)
        assert row["returncode"] != 0, row
        log = Path(row["log"]).read_text()
        assert "error:" in log and ("decide" in log if name.startswith("Semantic") else "True.intro" in log), row
    result = dict(timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  status="PASS", finite_source_equalities=len(fixtures)+len(corpus),
                  semantic_false_caught=2, malformed_proof_caught=1, runs=rows)
    (BASE / "results/lean-checks.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k != "runs"}))

if __name__ == "__main__":
    main()
