#!/usr/bin/env python3
"""One-shot source-pinned Lean replay, with review-owned sources and outputs."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
FAMILY = HERE.parent
RMAF = FAMILY.parents[1]
ROOT = RMAF.parents[1]
RESULT = RMAF / "results" / "triple-family-fresh-lean.json"
SOURCE = HERE / "source"
BUILD = HERE / "build"
LOGS = HERE / "logs"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    assert not RESULT.exists(), "preserve prior receipt"
    for directory in (SOURCE, BUILD, LOGS):
        directory.mkdir(exist_ok=True)
    old = json.loads((RMAF / "results/triple-family-lean-v1.json").read_text())
    deps = json.loads((RMAF / "results/triple-dp-connected-lean.json").read_text())
    dep_pins = {row["file"]: row["sha256"] for row in deps["builds"] if not row["negative"]}
    inputs = []
    for row in old["builds"]:
        src = ROOT / row["file"]
        assert sha(src) == row["sha256"], src
        if row["dependency"]:
            assert sha(src) == dep_pins[src.name], src
        snapshot = SOURCE / src.name
        assert not snapshot.exists(), snapshot
        snapshot.write_bytes(src.read_bytes())
        inputs.append((src, snapshot, row["dependency"], row["negative"]))
    inputs.append((HERE / "CleanFamily.lean", HERE / "CleanFamily.lean", False, False))
    env = dict(os.environ, ELAN_HOME=str(ROOT / ".runtime/elan"), LEAN_PATH=str(BUILD))
    version = subprocess.run([str(ROOT / "bootloops-lean"), "--version"], cwd=ROOT,
                             env=env, capture_output=True, text=True, timeout=20)
    assert version.returncode == 0 and "4.35.0" in version.stdout
    builds = []
    for original, src, dependency, negative in inputs:
        text = src.read_text()
        assert not re.search(r"\b(?:sorry|admit|native_decide)\b", text)
        assert not re.search(r"^\s*axiom\b", text, re.M)
        command = [str(ROOT / "bootloops-lean")]
        if not negative:
            command += ["-o", str(BUILD / (src.stem + ".olean"))]
        command.append(str(src))
        started = time.perf_counter()
        proc = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True, timeout=20)
        log = proc.stdout + proc.stderr
        log_path = LOGS / (src.stem + ".log")
        log_path.write_text(log)
        if negative:
            assert proc.returncode != 0
            assert "0 = 1" in log and "is false" in log and "decide" in log, log
            assert "unknown module" not in log and "unknown identifier" not in log, log
        else:
            assert proc.returncode == 0, log
            assert "sorryAx" not in log, log
        found = []
        for line in log.splitlines():
            match = re.fullmatch(r"'([^']+)' depends on axioms: \[(.*)\]", line)
            empty = re.fullmatch(r"'([^']+)' does not depend on any axioms", line)
            if match or empty:
                name = (match or empty).group(1)
                axioms = [x.strip() for x in match.group(2).split(",")] if match else []
                assert set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}, line
                found.append({"name": name, "axioms": axioms})
        prints = re.findall(r"^#print axioms (\w+)$", text, re.M)
        assert len(found) == len(prints), (src, prints, found)
        assert [f["name"].rsplit(".", 1)[-1] for f in found] == prints
        builds.append({"original": str(original.relative_to(ROOT)), "source_snapshot": str(src.relative_to(ROOT)),
                       "sha256": sha(src), "dependency": dependency, "negative": negative,
                       "returncode": proc.returncode, "seconds": time.perf_counter() - started,
                       "command": command, "log": str(log_path.relative_to(ROOT)), "audits": found})
    family = [a for b in builds if not b["dependency"] for a in b["audits"]]
    imported = [a for b in builds if b["dependency"] for a in b["audits"]]
    assert len(family) == 31 and len(imported) == 27
    assert sum(a["name"] == "TripleDP.Family.normalize" for a in family) == 1
    for original, snapshot, _, _ in inputs:
        assert sha(original) == sha(snapshot), "source changed during replay"
    receipt = {"schema": 1, "created_utc": datetime.now(timezone.utc).isoformat(),
               "version": version.stdout.strip(), "environment": {k: env[k] for k in ("ELAN_HOME", "LEAN_PATH")},
               "new_family_audited_declarations": 31, "new_family_audited_theorems": 30,
               "new_family_audited_constructor": "TripleDP.Family.normalize", "dependency_audits": 27,
               "negative": "actual 0 = 1 rejected by decide", "clean_twin": "0 = 0 accepted by decide",
               "scope": "Raw-to-retained family normalization only; no claim of full G2 or Python correctness",
               "builds": builds, "rebuild_sha256": sha(Path(__file__))}
    RESULT.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"family_audits": len(family), "dependency_audits": len(imported),
                      "negative_rejected": True, "clean_twin_passed": True, "receipt": str(RESULT)}))


if __name__ == "__main__":
    main()
