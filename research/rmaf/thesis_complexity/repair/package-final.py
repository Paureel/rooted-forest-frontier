"""Package executed repair evidence; no scientific checks are inferred from packaging."""
from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / "research/rmaf"
REPAIR = BASE / "thesis_complexity/repair"
RESULTS = BASE / "results"


def read(path: Path):
    return json.loads(path.read_text())


def sha(path: Path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative(path: Path):
    return str(path.relative_to(ROOT))


def atomic(path: Path, value):
    temp = path.with_suffix(path.suffix + ".tmp")
    temp.write_text(json.dumps(value, indent=2) + "\n")
    temp.replace(path)


source = BASE / "sources/baseline/whidden-thesis-2013.pdf"
controls = REPAIR / "controls-frozen.json"
assert sha(source) == "0dd9ced63f26ab608dc484cfe853d52171565b0cc704bb61336dd64a15c2bbe9"
assert sha(controls) == "a96b66716ec2b1f2c68ce38461413859bd3ca7bb504d7f2b4f6ca85f29e55185"

history = read(RESULTS / "thesis-runtime-repair-fresh-review-history-final.json")
first_review = ROOT / history["first_review"]["receipt"]
assert sha(first_review) == history["first_review"]["sha256"]
assert history["metrics"]["exact_replay_checks"] == 60
assert history["metrics"]["actual_C_count"] == 2
assert history["fire"]["residual"] == 1

lean = read(RESULTS / "thesis-runtime-repair-fresh-review-history-lean.json")
assert lean["positive_exit_code"] == 0
assert lean["negative_exit_code"] != 0
assert lean["all_13_standard_axioms_only"]
assert sha(ROOT / lean["source"]) == lean["source_sha256"]
for run in read(RESULTS / "thesis-runtime-repair-parent-final-lean.json")["runs"]:
    assert run["exit_code"] == 0
    assert sha(ROOT / run["source"]) == run["sha256"]

# Dashboard corrections preserve the prior bytes and do not rewrite review receipts.
fresh_path = BASE / "progress/thesis-runtime-repair-fresh-review.json"
backup = RESULTS / "thesis-runtime-repair-fresh-review-progress-before-status-fix.json"
if not backup.exists():
    backup.write_bytes(fresh_path.read_bytes())
fresh = read(fresh_path)
for group in ("claims", "lemmas"):
    for item in fresh[group]:
        if item["id"] in ("history-outside-b-application", "active-a-history"):
            item["status"] = "refuted"
atomic(fresh_path, fresh)

progress_path = BASE / "progress/thesis-runtime-repair.json"
progress = read(progress_path)
progress.update(
    status="open",
    summary=("Reviewed repair pass complete. Conditional arithmetic is checked; a reachable "
             "twelve-leaf history refutes universal outside-sibling application. Its C subtree "
             "has two calls. The joint and full runtime bounds remain open."),
)
progress["metrics"].update(
    active_child_agents=0,
    new_history_independent_checks=60,
    new_history_independent_lean_checks=13,
    new_history_application_counterexamples=1,
    new_history_actual_C_calls=2,
)
progress["claims"] = [
    {"id": "joint-g4-bound", "label": "Joint G4 descendant bound", "status": "open",
     "detail": "Inside-sibling continuation, credited A allowance, annotation closure and global induction remain unproved."},
    {"id": "conditional-composition", "label": "Conditional A/B/C count composition", "status": "checked",
     "detail": "Writing X=alpha*2^K: A<=X/4-2, B<=X/8-3, C<=X/8+2 imply 1+A+B+C<=X/2-2. This does not supply structural premises."},
    {"id": "outside-sibling-application", "label": "Universal outside-sibling application premise", "status": "refuted",
     "detail": "Independent 60-check replay of an unprotected twelve-leaf C,A,C,A history reaches J with retained x inside protected sibling b. Conditional geometry and runtime inequality are not refuted."},
    {"id": "history-finite-certificate", "label": "Concrete reachable history certificate", "status": "checked",
     "detail": "11 finite Lean facts plus two independent supplemental checks pass using only propext or no axioms; false outside-b certificate rejected. Source correspondence remains an explicitly reviewed interpretation, not a universal Lean source model."},
]
progress["lemmas"] = [
    {"id": "inside-sibling-prefix", "label": "Inside-sibling C-prefix certificate", "status": "open",
     "detail": "For every reachable exceptional J with x inside b, cover every legal C continuation and prove its exact affine frontier allowance; retain physical protections through empty-credit resets."},
    {"id": "credited-A", "label": "Credited A continuation allowance", "status": "open",
     "detail": "Prove I(A)<=alpha*2^(K-2)-2 or supply a compatible prefix certificate. Empty-credit outer induction alone is insufficient."},
]
additional = [
    relative(REPAIR / "report.md"), relative(REPAIR / "open-lemmas.md"),
    relative(REPAIR / "fresh_review/new_history/ADDENDUM.md"),
    relative(RESULTS / "thesis-runtime-repair-fresh-review-history-final.json"),
    relative(RESULTS / "thesis-runtime-repair-fresh-review-history-lean.json"),
    relative(RESULTS / "thesis-runtime-repair-summary.json"),
]
progress["artifacts"] = list(dict.fromkeys(progress["artifacts"] + additional))
atomic(progress_path, progress)

allowed_statuses = {"running", "active", "open", "tested", "refuted", "checked", "complete", "conditional", "pending", "source-reported"}
dashboard_paths = sorted((BASE / "progress").glob("thesis-runtime-repair*.json"))
for path in dashboard_paths:
    record = read(path)
    for key in ("id", "title", "status", "summary", "metrics", "artifacts"):
        assert key in record, (path, key)
    assert record["status"] in allowed_statuses, path
    assert isinstance(record["metrics"], dict), path
    for key in ("claims", "lemmas"):
        for claim in record.get(key, []):
            assert all(field in claim for field in ("id", "label", "status", "detail")), (path, claim)

receipt_names = [
    "thesis-runtime-repair-controls.json",
    "thesis-runtime-repair-adversary-final.json",
    "thesis-runtime-repair-geometry-final.json",
    "thesis-runtime-repair-recurrence-summary.json",
    "thesis-runtime-repair-fresh-review-final.json",
    "thesis-runtime-repair-history-reachable-probe.json",
    "thesis-runtime-repair-history-lean.json",
    "thesis-runtime-repair-fresh-review-history-replay.json",
    "thesis-runtime-repair-fresh-review-history-lean.json",
    "thesis-runtime-repair-fresh-review-history-final.json",
    "thesis-runtime-repair-parent-final-lean.json",
    "thesis-runtime-repair-parent-adversary-axioms.json",
]
evidence_paths = [RESULTS / name for name in receipt_names] + [
    source, controls, REPAIR / "HistoryTrace.lean", REPAIR / "FalseHistoryTrace.lean",
    REPAIR / "report.md", REPAIR / "history-counterexample.md", REPAIR / "open-lemmas.md",
    REPAIR / "WORKFILE.md", REPAIR / "import-ledger.md", REPAIR / "review-queue.md",
    REPAIR / "geometry/Geometry.lean", REPAIR / "recurrence/RepairArithmetic.lean",
    REPAIR / "adversary/AdversaryArithmetic.lean", REPAIR / "fresh_review/new_history/ADDENDUM.md",
    REPAIR / "package-final.py",
]
manifest = {
    "id": "thesis-runtime-repair-manifest",
    "generated_at": datetime.now(timezone.utc).isoformat(),
    "files": [{"path": relative(path), "sha256": sha(path)} for path in evidence_paths],
    "source_and_frozen_controls_unchanged": True,
    "first_review_receipt_unchanged": True,
}
atomic(REPAIR / "manifest.json", manifest)
summary = {
    "id": "thesis-runtime-repair-summary",
    "title": "Reviewed joint G4 runtime repair",
    "status": "open",
    "execution_status": "completed-reviewed-pass",
    "summary": progress["summary"],
    "convention": "labelled unary rho root; thesis cut budget K; full permitted recursive-call tree",
    "metrics": progress["metrics"],
    "claims": progress["claims"],
    "lemmas": progress["lemmas"],
    "reachable_counterexample": history["fire"],
    "counterexample_actual_C_calls": 2,
    "formal_scope": lean["limits"],
    "conditional_interface": {
        "X": "alpha*2^K", "A": "X/4-2", "B": "X/8-3", "sufficient_C": "X/8+2",
        "target": "1+A+B+C<=X/2-2",
        "prefix_sufficient_conditions": ["sum(2^-d)<=1/4", "V-3L<=2"],
        "imports": "valid smaller-budget empty-credit exit bounds, source-valid prefix and credited A allowance",
    },
    "independence": {
        "adversary": "fresh source/fixture reconstruction before real search",
        "proof_routes": "isolated geometry and recurrence routes, no cross-reading while active",
        "first_review": "fresh source evaluator before candidate details; finite scope explicitly bounded",
        "new_history_discovery": "coordinator reused geometry evaluator; not independent",
        "new_history_review": history["implementation_lineage"],
        "coordinator_Lean_replays": "same-source compilation checks, not independent source-to-model proof",
    },
    "limits": [
        "No universal joint G4 bound or full O(2^K n) theorem established or refuted.",
        "No exhaustive arbitrary-size, arbitrary-forest or every-tie-policy search claimed.",
        "Finite Lean tree certificates and conditional arithmetic are not a universal Lean source-algorithm model.",
        "Source page119 prose/equation Q conflict remains; the new history does not use it.",
        "Original source per-invocation O(n), full global induction and parameter transfer remain separate obligations.",
        "Additional focused adversary/follow-up could not start because of shared agent-thread limit; independent existing reviewer follow-up completed.",
    ],
    "preservation": {
        "original_sources_receipts_unchanged": True,
        "failed_formulations_and_negative_logs_retained": True,
        "aggregate_theorem_count_changed": False,
        "upstream_toolkit_modified": False,
    },
    "packaging_checks": {"dashboard_records_validated": len(dashboard_paths), "source_hash_verified": True, "control_hash_verified": True, "first_review_hash_verified": True},
    "artifacts": [relative(REPAIR / "manifest.json")] + [relative(path) for path in evidence_paths],
}
atomic(RESULTS / "thesis-runtime-repair-summary.json", summary)
print(json.dumps({"summary": relative(RESULTS / "thesis-runtime-repair-summary.json"),
                  "status": summary["status"], "manifest_files": len(evidence_paths),
                  "dashboard_records_validated": len(dashboard_paths),
                  "source_and_controls_unchanged": True,
                  "history_premise": "refuted", "runtime_bound": "open"}, indent=2))
