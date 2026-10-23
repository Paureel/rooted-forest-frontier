from pathlib import Path
from hashlib import sha256
from datetime import datetime, timezone
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[5]

def digest(p):
    return sha256(p.read_bytes()).hexdigest()

pins = [
    ("research/rmaf/algorithm/verification/forest-reductions-2026-10-15/sol-frozen-ready-v1/READY-MANIFEST-v1.json", "25673f06bb120f25235aba32781acd07654fa44d98e258f96eba74a8fcbfce78", "files", 264, False),
    ("research/rmaf/algorithm/verification/forest-reductions-2026-10-15/sol-frozen-review-v1/REVIEW-MANIFEST-v1.json", "92618ee90023319c7d94732483738756cac35406541d80ca5dfadbc1f0523120", "files", 147, False),
    ("research/rmaf/algorithm/universal233/state_reductions/STATE-MANIFEST-v1.json", "9a85af84a6cd917af0780c4c12ab356897a7e416b402fa3f875250487f7c29f6", "immutable_files", 77, True),
    ("research/rmaf/algorithm/universal233/state_cherry_completion/CHERRY-MANIFEST-v1.json", "b9d584872792f5d6b8c00509c56160c47ac62732ef9a44f7c21c3b5717d53147", "immutable_files", 103, True),
]
records = []
for rel, expected, key, count, workspace_paths in pins:
    p = ROOT / rel
    assert digest(p) == expected, ("manifest drift", rel)
    data = json.loads(p.read_text())
    assert len(data[key]) == count
    base = ROOT if workspace_paths else p.parent
    for e in data[key]:
        f = base / e["path"]
        assert digest(f) == e["sha256"], ("artifact drift", str(f))
        if "bytes" in e:
            assert f.stat().st_size == e["bytes"]
    records.append({"manifest": rel, "sha256": expected, "entriesChecked": count, "allMatched": True})
instrument_pins = []
for version, expected, count in [
    (1, "fc2799fe7125a7ba478abbb5347e3b5914cf0dc0ab47b2c441d31945c33a07ca", 27),
    (2, "15956bac38c88ecabacac8d02223120ccf8a26bea146e292c5cea1d8d414716a", 31),
    (3, "23d7aae584e6f9e5783967f0638f01c4a2ceda07ef32bef6c7abeaec0aa422be", 84),
]:
    p = HERE / f"INSTRUMENTS-MANIFEST-v{version}.json"
    assert digest(p) == expected, ("instrument manifest drift", version)
    data = json.loads(p.read_text())
    assert len(data["files"]) == count
    for e in data["files"]:
        f = HERE / e["path"]
        assert digest(f) == e["sha256"], ("instrument drift", version, e["path"])
        assert f.stat().st_size == e["bytes"]
    instrument_pins.append({"manifest": p.name, "sha256": expected, "entriesChecked": count, "allMatched": True})
out = {"status": "PRESERVATION-PASS", "checkedUTC": datetime.now(timezone.utc).isoformat(), "priorFrozenSets": records, "currentInstrumentPins": instrument_pins, "allGoodCandidateContact": False, "method": "Manifest JSON parsed and listed file bytes hashed only; no new scientific source or result interpretation."}
(HERE / "PRESERVATION-v1.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({"status": out["status"], "priorEntriesMatched": sum(x["entriesChecked"] for x in records), "instrumentEntriesMatched": sum(x["entriesChecked"] for x in instrument_pins)}))
