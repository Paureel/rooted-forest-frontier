#!/usr/bin/env python3
"""Fresh-build the exact executable connectivity interface and its controls.

This audit checks typed statements and diagnostic provenance. Mathematical
interpretation is separately reviewed; this script does not close MAF geometry.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


ROOT = Path(__file__).resolve().parents[4]
BASE = Path(__file__).resolve().parent
STAMP = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
RUN = BASE / "audit" / STAMP
DEPS = RUN / "deps"
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
AXIOM_PATTERN = re.compile(
    r"'([^']+)' (does not depend on any axioms|depends on axioms: \[[^\]]*\])",
    re.S,
)


def relative(path: Path) -> str:
    return str(path.relative_to(ROOT))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def explicit_false(exit_code: int, log: str) -> bool:
    """Do not turn arbitrary elaboration failure into negative-control credit."""
    return (
        exit_code != 0
        and log.count(": error:") == 1
        and re.search(
            r"error: Tactic `decide` proved that the proposition\n[\s\S]+?\nis false(?:\n|$)",
            log,
        ) is not None
    )


def main() -> None:
    DEPS.mkdir(parents=True, exist_ok=False)
    started = time.perf_counter()
    env = os.environ.copy()
    # Every campaign import resolves only to this run's freshly built files.
    env["LEAN_PATH"] = str(DEPS)
    receipt = {
        "status": "pending",
        "scope": "Exact RMAF.minimalVertices connectivity, selected-leaf nonemptiness, "
                 "support membership preservation and original deepest-root consumer",
        "not_established": ["least connected hull", "unique-label interpretation",
                            "source/target restriction transport", "G2–G7",
                            "safe cover", "unrestricted complexity", "novelty"],
        "run_directory": relative(RUN),
        "source_hashes": {},
        "builds": {},
        "axioms": {},
        "false_controls": {},
        "parser_controls": {},
    }
    controls = json.loads((BASE / "audit-controls.json").read_text())
    for case in controls["planted_diagnostics"]:
        actual = explicit_false(case["exit"], case["message"])
        assert actual == case["accepted"], case["name"]
        receipt["parser_controls"][case["name"]] = {"expected": case["accepted"], "actual": actual}

    modules = [
        ("RMAF", ROOT / "research/rmaf/lean/RMAF.lean"),
        ("PureBridge", ROOT / "research/rmaf/pure_bridge/lean/PureBridge.lean"),
        ("GraphRegion", ROOT / "research/rmaf/bridge_review/lean/GraphRegion.lean"),
        ("ExtractorControls", BASE / "lean/ExtractorControls.lean"),
        ("ExecutableConnectivity", BASE / "lean/ExecutableConnectivity.lean"),
    ]
    false_paths = sorted((BASE / "lean/negative").glob("*.lean"))
    malformed = BASE / "lean/malformed/UnknownProof.lean"
    sources = [p for _, p in modules] + false_paths + [malformed, BASE / "audit.py",
               BASE / "CONTROLS.json", BASE / "audit-controls.json"]
    for path in sources:
        receipt["source_hashes"][relative(path)] = digest(path)
    expected_control_hash = (BASE / "controls.sha256").read_text().split()[0]
    assert digest(BASE / "CONTROLS.json") == expected_control_hash
    receipt["frozen_control_hash_matched"] = True

    for _, path in modules:
        assert not re.search(r"^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b",
                             path.read_text(), re.M), relative(path)

    def execute(name: str, path: Path, output: Path | None = None) -> tuple[int, str, dict]:
        args = [str(ROOT / "bootloops-lean")]
        if output is not None:
            args += ["-o", str(output)]
        args.append(str(path))
        begin = time.perf_counter()
        result = subprocess.run(args, cwd=ROOT, env=env, text=True, capture_output=True, timeout=60)
        log = result.stdout + result.stderr
        logpath = RUN / (name + ".log")
        logpath.write_text(log)
        record = {"exit_code": result.returncode, "seconds": time.perf_counter() - begin,
                  "log": relative(logpath), "log_sha256": digest(logpath)}
        return result.returncode, log, record

    version = subprocess.run([str(ROOT / "bootloops-lean"), "--version"], cwd=ROOT,
                             env=env, text=True, capture_output=True, check=True, timeout=60)
    receipt["lean_version"] = version.stdout.strip()
    (RUN / "version.log").write_text(version.stdout + version.stderr)
    for name, path in modules:
        code, log, record = execute(name, path, DEPS / (name + ".olean"))
        assert code == 0, (name, log)
        assert "sorryAx" not in log and ": error:" not in log, (name, log)
        found = {}
        for theorem, body in AXIOM_PATTERN.findall(log):
            axioms = [] if body.startswith("does not") else [
                x.strip() for x in body.split("[", 1)[1].rstrip("]").split(",")]
            assert set(axioms) <= ALLOWED_AXIOMS, (theorem, axioms)
            found[theorem] = axioms
        expected = re.findall(r"^#print axioms (\S+)", path.read_text(), re.M)
        assert len(found) == len(expected), (name, len(found), len(expected))
        for declaration in expected:
            assert any(k == declaration or k.endswith("." + declaration) for k in found), declaration
        receipt["axioms"].update(found)
        record["axiom_reports"] = len(found)
        receipt["builds"][name] = record

    for path in false_paths:
        code, log, record = execute(path.stem, path)
        assert explicit_false(code, log), (path.name, log)
        record.update(rejected_as_false=True, positive_twin=controls["true_twins"][path.stem])
        receipt["false_controls"][path.stem] = record
    code, log, record = execute("MalformedUnknownProof", malformed)
    assert code != 0 and "Unknown identifier" in log, log
    assert not explicit_false(code, log), log
    record.update(rejected_as_falsity_receipt=True)
    receipt["malformed_diagnostic_control"] = record

    for path in sources:
        assert receipt["source_hashes"][relative(path)] == digest(path), relative(path)
    receipt["new_theorem_count"] = sum(
        len(re.findall(r"^theorem\s", path.read_text(), re.M)) for _, path in modules[-2:])
    receipt["new_axiom_report_count"] = sum(receipt["builds"][name]["axiom_reports"]
                                             for name, _ in modules[-2:])
    receipt["seconds"] = time.perf_counter() - started
    receipt["status"] = "kernel-checked-executable-interface"
    receipt["semantic_review"] = "separate and pending at audit creation"
    output = json.dumps(receipt, indent=2) + "\n"
    (RUN / "certificate.json").write_text(output)
    (BASE / "audit/certificate.json").write_text(output)
    (ROOT / "research/rmaf/results/bridge-executable-lean.json").write_text(output)
    print(json.dumps({"status": receipt["status"], "new_theorems": receipt["new_theorem_count"],
                      "false_controls": len(receipt["false_controls"]),
                      "malformed_control_rejected": True, "seconds": receipt["seconds"]}))


if __name__ == "__main__":
    main()
