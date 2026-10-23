"""One-use frame-review evidence retrieval; no theorem or kernel replay.

Toolkit index and emitall GUIDE consulted; neither supplies project manifest
and retained-type retrieval. Controls test this byte/JSON comparator only.
"""
from pathlib import Path
import gzip
import hashlib
import json
import time

ROOT = Path(__file__).resolve().parents[5]
OUT = Path(__file__).resolve().parent
A = ROOT / "research/rmaf/algorithm/universal233/output_state"
R = ROOT / "research/rmaf/algorithm/verification/output-state-2026-10-15/frozen-review-v1"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check_bytes(data, expected):
    if digest(data) != expected:
        raise ValueError("SHA256 mismatch")


def parse_reads(text):
    out = {}
    for line in text.splitlines():
        if line.startswith("READ|"):
            _, key, value = line.split("|", 2)
            if key in out:
                raise ValueError("duplicate readout")
            out[key] = json.loads(value)
    if not out:
        raise ValueError("empty readout bank")
    return out


started = time.monotonic()
controls = []
# These plants precede this script's real comparisons, but follow document
# contact. They receive no blind-control or independent-replication credit.
known_sha = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
check_bytes(b"abc", known_sha)
controls.append("known SHA256 abc clean twin accepted")
try:
    check_bytes(b"abd", known_sha)
except ValueError:
    controls.append("altered-byte SHA256 twin rejected")
else:
    raise AssertionError("digest comparator accepted corrupted bytes")
assert parse_reads('READ|zero|{"n":0}') == {"zero": {"n": 0}}
for text in ('READ|zero|{"n":0}\nREAD|zero|{"n":0}', 'READ|zero|{', ''):
    try:
        parse_reads(text)
    except (ValueError, json.JSONDecodeError):
        controls.append("malformed/duplicate/empty readout rejected")
    else:
        raise AssertionError("parser accepted planted corruption")

am_bytes = (A / "OUTPUT-STATE-MANIFEST-v1.json").read_bytes()
rm_bytes = (R / "MANIFEST.json").read_bytes()
check_bytes(am_bytes, "d27ae69ef54c6c03f20c43767fc0b731e5ff96abcfa59f1f426223c77e6a67f5")
check_bytes(rm_bytes, "f85ffa44ccc00d8244608f3b5eef2b32330d9540f3bbe4ab2efa70d7911d1a99")
am = json.loads(am_bytes)
rm = json.loads(rm_bytes)
assert len(am["immutable_files"]) == am["entry_count"] == 313
assert len(rm["files"]) == 338
apins = {e["path"]: e["sha256"] for e in am["immutable_files"]}
rpins = rm["files"]

aselected = ["RESULT.md", "INTERFACE.md", "FIRST-GAP.md", "OutputDefs.lean",
             "Materialize.lean", "Equivalence.lean", "ResidualConsumer.lean"]
rselected = ["review-v1/" + p for p in (
    "SEMANTIC-REVIEW-v1.md", "CONSUMER-TRACE-v2.md", "RUNTIME-REVIEW-v1.md",
    "CONTACTS-AND-CORRECTIONS-v1.md", "ORIGIN-BODY-COVERAGE-CORRECTION-v1.json",
    "AUTHOR-certificate.json",
    "isolated-source-v1/FreshActualReadoutsV2.log",
    "isolated-source-v1/FreshEveryOutputConsumerV1.log",
    "isolated-source-v1/FreshEveryOutputConsumerV1.lean",
    "isolated-source-v1/GroupState.lean", "isolated-source-v1/GroupPriority.lean",
    "isolated-source-v1/SelectedContinuation.lean", "isolated-source-v1/RMAF.lean")]
rselected += ["results/" + p for p in (
    "algorithm-output-state-fresh-actual-readouts-v2.json",
    "algorithm-output-state-fresh-every-output-v1.json",
    "algorithm-output-state-fresh-origin-audit-v4.json.gz")]
pins = []
for owner, base, names, source in (("author", A, aselected, apins),
                                  ("review", R, rselected, rpins)):
    for name in names:
        path = base / name
        key = str(path.relative_to(ROOT)) if owner == "author" else name
        expected = source[key]
        data = path.read_bytes()
        check_bytes(data, expected)
        pins.append({"owner": owner, "path": str(path.relative_to(ROOT)),
                     "sha256": expected, "bytes": len(data)})

readpath = R / "review-v1/isolated-source-v1/FreshActualReadoutsV2.log"
reads = parse_reads(readpath.read_text())
receipt = json.loads((R / "results/algorithm-output-state-fresh-actual-readouts-v2.json").read_text())
assert len(reads) == receipt["readout_denominator"] == 72
assert reads == receipt["readouts"]
assert receipt["comparison_denominator"] == receipt["comparisons_passed"] == 304
# These are assertions about retained readouts, not new model evaluations.
assert reads["target_overlap_refined"]["state"] is True
assert reads["target_overlap_refined"]["target_Q_clear"] is False
assert reads["target_overlap_Q_invalid"]["state"] is False
assert reads["source_overlap_omitted_guard"]["state"] is True
assert reads["source_overlap_omitted_guard"]["original_AF"] is False
assert reads["empty_block_dropped_unchecked"]["Q_checked"] is False
assert reads["empty_block_dropped_unchecked"]["additional"] != reads["empty_block_dropped_unchecked"]["Q_subtraction"]
assert reads["group"]["B_internal_target_clear"] is False
assert reads["group"]["actual_sideOutputs_derived"] is False
assert reads["group"]["recursive_solver_implemented"] is False

every = json.loads((R / "results/algorithm-output-state-fresh-every-output-v1.json").read_text())
banks = every["banks"]
assert [b["q"] for b in banks] == list(range(8))
assert [b["output_denominator"] for b in banks] == [0,0,0,1,1,1,1,1]
assert sum(len(b["all_outputs"]) for b in banks) == every["finite_output_denominator"] == 5
assert every["internal_target_overlap_outputs"] == 0
for bank in banks:
    assert len(bank["all_outputs"]) == bank["output_denominator"]
    for item in bank["all_outputs"]:
        assert item["B_internal_target_clear"] is True
        assert item["all_owned_B_pieces_checked"] == 2

inventory = json.loads(gzip.decompress((R / "results/algorithm-output-state-fresh-origin-audit-v4.json.gz").read_bytes()))
names = ["OutputState.agrees_iff_original", "OutputState.every_opposite_residual_query",
         "ForestGroups.ResidualSolverContract"]
selected = [d for d in inventory["declarations"] if d["name"] in names]
assert {d["name"] for d in selected} == set(names)
assert all(d["type_expr"] for d in selected)
assert all(d["producer_source"] and d["producer_sha256"] for d in selected)
assert all(d["body_structural_hash64"] is not None for d in selected)

report = {
    "scope": "retained evidence/type/byte checks only; no fresh kernel replay or independent mathematical replication",
    "controls_after_document_contact": controls,
    "manifest_lengths": {"author_entries": 313, "review_entries": 338},
    "selected_pins": pins,
    "selected_pin_count": len(pins),
    "retained_readout_count": len(reads),
    "retained_comparison_count": receipt["comparison_denominator"],
    "named_readouts": {k: reads[k] for k in (
        "target_overlap_refined", "target_overlap_Q_invalid", "source_overlap_omitted_guard",
        "empty_block_dropped_unchecked", "group", "mock.q0_no_call", "mock.missing_contract_no_access")},
    "all_output_counts_q0_through_q7": [b["output_denominator"] for b in banks],
    "retained_inventory_summary_only": {k: inventory[k] for k in (
        "module_count", "declaration_count", "private_declarations", "recursors", "constructors",
        "canonical_names_origins_axioms_exact", "body_adapter_basis")},
    "retrieved_exact_type_and_body_records": selected,
    "elapsed_seconds": time.monotonic() - started,
    "verdict": "PASS_SELECTED_FRAME_EVIDENCE_CHECKS",
}
(OUT / "BOUNDED-CHECKS-v1.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({k: report[k] for k in ("verdict", "selected_pin_count", "retained_readout_count", "retained_comparison_count", "elapsed_seconds")}, indent=2))
