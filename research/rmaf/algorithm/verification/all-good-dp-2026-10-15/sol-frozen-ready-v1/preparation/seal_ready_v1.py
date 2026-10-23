from pathlib import Path
from hashlib import sha256
from datetime import datetime, timezone
import json
import shutil

H = Path(__file__).resolve().parent
TARGET = H.parent / "sol-frozen-ready-v1"
assert not TARGET.exists(), "Refuse to overwrite any existing READY snapshot"
summary = json.loads((H / "READY-SUMMARY-v2.json").read_text())
preserved = json.loads((H / "PRESERVATION-v1.json").read_text())
assert summary["candidateContact"] is False and summary["candidateCompiled"] is False
assert preserved["status"] == "PRESERVATION-PASS"
TARGET.mkdir()
prep = TARGET / "preparation"
prep.mkdir()
for p in sorted(H.rglob("*")):
    if not p.is_file() or "__pycache__" in p.parts or p.suffix == ".pyc":
        continue
    dest = prep / p.relative_to(H)
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(p, dest)
for name in ["TARGET-v1.md", "SOL-ALL-GOOD-DP-WORKFILE-v1.md"]:
    shutil.copyfile(H.parent / name, TARGET / name)
files = []
for p in sorted(TARGET.rglob("*")):
    if p.is_file():
        files.append({"path": p.relative_to(TARGET).as_posix(), "bytes": p.stat().st_size, "sha256": sha256(p.read_bytes()).hexdigest()})
manifest = {
    "status": "PRE-CANDIDATE-CONTROLS-READY",
    "freezeUTC": datetime.now(timezone.utc).isoformat(),
    "artifactCount": len(files),
    "files": files,
    "candidateReleased": False,
    "candidateContact": False,
    "candidateCompiled": False,
    "scientificGrade": "CONTROL_READINESS_ONLY",
    "allThreeMainMilestones": "OPEN",
    "novelty": "OPEN",
    "verifiedClosed": False,
    "summary": summary,
    "preservation": preserved,
    "releaseNeeded": "Separate root release of the exact final232 completed all_good_dp source/dependency manifest. No self-release.",
    "laterFreshContextProseReferee": "Reserved to separate root assignment after candidate source report sealing; no credit claimed by this preparation arm.",
    "limitations": ["Fixed n<=4 controls only; no general scientific candidate verdict.", "Own checker/auditor reuse gives zero extra independent replications.", "Literal generated-definition forcing disclosed; no all-possible compiler-synthetic-equation completeness claim.", "Initial import failure and first full-run timing-record omission preserved; final timed replay was projected before launch.", "No polynomial or machine-runtime claim from finite timings; candidate runtime closure and polynomial contract await release.", "Only emitall/gatekeeper toolkit selftests run, not the full toolkit suite."]
}
mp = TARGET / "READY-MANIFEST-v1.json"
mp.write_text(json.dumps(manifest, indent=2) + "\n")
mh = sha256(mp.read_bytes()).hexdigest()
(TARGET / "READY-MANIFEST-v1.sha256").write_text(f"{mh}  READY-MANIFEST-v1.json\n")
for entry in files:
    p = TARGET / entry["path"]
    assert sha256(p.read_bytes()).hexdigest() == entry["sha256"] and p.stat().st_size == entry["bytes"]
for p in TARGET.rglob("*"):
    if p.is_file():
        p.chmod(0o444)
for p in sorted((p for p in TARGET.rglob("*") if p.is_dir()), key=lambda p: len(p.parts), reverse=True):
    p.chmod(0o555)
TARGET.chmod(0o555)
print(json.dumps({"status": manifest["status"], "manifest": str(mp), "sha256": mh, "artifacts": len(files), "candidateContact": False, "candidateCompiled": False}))
