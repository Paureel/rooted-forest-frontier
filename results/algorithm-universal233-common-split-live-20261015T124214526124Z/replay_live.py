"""Partial author development replay; explicitly not a final acceptance audit."""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[5]
SRC = Path(__file__).resolve().parent
DEP = ROOT / "results/algorithm-universal233-both-bad-20261015T115125Z"
ORDER = ["Controls", "Rename", "CrossingCount", "Marked", "Clip", "Deletion",
         "MarkerSingleton", "MarkerBounds", "Port", "OriginalPort", "PortSingleton",
         "MixedPort", "CutHull", "ForestMerge", "MarkedLift", "StableMarker", "ClipCount"]

def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main() -> None:
    now = datetime.now(timezone.utc)
    out = ROOT / "results" / ("algorithm-universal233-common-split-live-" + now.strftime("%Y%m%dT%H%M%S%fZ"))
    out.mkdir()
    inputs = []
    for p in sorted(SRC.iterdir()):
        if p.is_file():
            shutil.copy2(p, out / p.name)
            inputs.append({"path": str(p.relative_to(ROOT)), "sha256": sha(p)})
    base = json.loads((DEP / "certificate.json").read_text())
    deps = []
    for name in base["positive_order"]:
        source, binary = DEP / f"{name}.lean", DEP / f"{name}.olean"
        deps.append({"module": name, "source": str(source.relative_to(ROOT)),
                     "source_sha256": sha(source), "binary": str(binary.relative_to(ROOT)),
                     "binary_sha256": sha(binary), "rebuilt_here": False})
    old = ROOT / "results/algorithm-universal233-output-state-20261015T105826Z"
    old_certificate = json.loads((old / "certificate.json").read_text())
    common_names = sorted(set(old_certificate["positive_order"]) & set(base["positive_order"]))
    common = [(name, sha(old/f"{name}.lean"), sha(DEP/f"{name}.lean")) for name in common_names]
    mismatches = [row for row in common if row[1] != row[2]]
    assert not mismatches, mismatches
    env = dict(os.environ, LEAN_PATH=f"{out}:{DEP}")
    runs = []
    for name in ORDER + ["AxiomsLive", "FalseControls"]:
        start = time.monotonic()
        cmd = [str(ROOT / "bootloops-lean"), "-o", str(out / f"{name}.olean"), str(out / f"{name}.lean")]
        r = subprocess.run(cmd, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / f"{name}.log").write_text(r.stdout)
        runs.append({"module": name, "exit": r.returncode, "seconds": time.monotonic()-start,
                     "source_sha256": sha(out / f"{name}.lean"), "log_sha256": sha(out/f"{name}.log")})
        if name == "FalseControls":
            assert r.returncode != 0 and r.stdout.count("error:") == 5, r.stdout
        else:
            assert r.returncode == 0, (name, r.stdout)
    axioms = (out / "AxiomsLive.log").read_text()
    assert "sorryAx" not in axioms
    receipt = {
        "status": "LIVE_PARTIAL_AUTHOR_COMPILE_ONLY",
        "utc": now.isoformat(), "complete_algorithm": False,
        "all_three_main_milestones": "OPEN", "independent_acceptance": False,
        "final_producer_occurrence_audit": "NOT_RUN; required before final freeze",
        "positive_new_modules_rebuilt": len(ORDER), "original_positive_control_groups": 9,
        "original_false_claims_rejected": 5, "selected_axiom_closures_printed": 11,
        "axiom_scope": "selected theorem dependency closures only; not all producer occurrences",
        "dependency_scope": "exact frozen160 source+binary hashes recorded; binaries reused, not rebuilt here",
        "shared_completed_output_source_files_compared": len(common), "shared_source_mismatches": mismatches,
        "inputs": inputs, "frozen_dependencies": deps, "runs": runs,
        "first_gap": "Actual marked-minimum families and optimal crossing-AF projection must be bound into same-list port/merge consumers; exact global minimum formula and Rule5.3.1 applicability remain OPEN",
    }
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2)+"\n")
    print(json.dumps({"path": str(out.relative_to(ROOT)), "status": receipt["status"],
                      "new_modules": len(ORDER), "false_rejected": 5, "dependencies_rebuilt": False}))

if __name__ == "__main__":
    main()
