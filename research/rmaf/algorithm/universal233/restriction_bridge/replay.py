#!/usr/bin/env python3
"""One-shot literal restriction proof replay, adapted from completed source_coverage/replay.py.

This problem-specific script snapshots only the public target, local sources,
original RMAF and frozen geometry dependencies. It retains development/false
failures, rebuilds in an isolated search path, and audits every declaration by
its actual module origin. Author replay is not fresh nonauthor verification.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BASE = HERE.parent
SPECS = [("RMAF", ROOT / "research/rmaf/lean/RMAF.lean")]
SPECS += [(n, BASE / "geometry" / (n + ".lean")) for n in ["Geometry", "Bridge", "Composition"]]
SPECS += [(n, HERE / (n + ".lean")) for n in ["Restriction", "Embedding", "Partition", "Cost", "Forward", "Reconstruction", "Controls", "Consumers"]]
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def clean(s):
    s = re.sub(r"/\-.*?\-/", lambda m: "\n" * m.group().count("\n"), s, flags=re.S)
    return re.sub(r"--[^\n]*", "", s)

stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
OUT = HERE / "replay" / stamp
OUT.mkdir(parents=True, exist_ok=False)
(HERE / "LATEST-REPLAY.txt").write_text(str(OUT) + "\n")
ENV = dict(os.environ, LEAN_PATH=str(OUT))
record = {"status": "RUNNING", "grade": "AUTHOR_KERNEL_REPLAY_ONLY; fresh nonauthor review pending",
          "target": "TARGET-v1.md", "all_three_main_milestones": "OPEN", "builds": [], "controls": {},
          "input_hashes": {}, "forward_decomposition": False, "reverse_reconstruction": False}

def save():
    (OUT / "certificate.json").write_text(json.dumps(record, indent=2) + "\n")

def run(n, build=False):
    args = [str(ROOT / "bootloops-lean")]
    if build:
        args += ["-o", str(OUT / (n + ".olean"))]
    args += [str(OUT / (n + ".lean"))]
    start = time.monotonic()
    p = subprocess.run(args, cwd=OUT, env=ENV, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=60)
    (OUT / (n + ".log")).write_text(p.stdout)
    record["builds"].append({"module": n, "returncode": p.returncode,
                             "seconds": round(time.monotonic() - start, 6)})
    save()
    return p

manifest_path = BASE / "INTEGRATION-MANIFEST-v1.json"
manifest = json.loads(manifest_path.read_text())
frozen = {row["path"]: row["sha256"] for row in manifest["immutable_files"]}
for _, path in SPECS[:4]:
    rel = str(path.relative_to(ROOT))
    assert rel in frozen and digest(path) == frozen[rel], "frozen source mismatch: " + rel
record["frozen_manifest_sha256"] = digest(manifest_path)
for n, path in SPECS:
    assert not re.search(r"\b(sorry|admit|axiom|native_decide)\b", clean(path.read_text())), str(path)
    (OUT / (n + ".lean")).write_bytes(path.read_bytes())
for path in [*(p for _, p in SPECS), HERE / "FalseControls.lean", HERE / "TARGET-v1.md",
             HERE / "CONTROLS-v1.md", Path(__file__), ROOT / "bootloops-lean",
             ROOT / "bootloops-lake", ROOT / "bootloops-python"]:
    record["input_hashes"][str(path.relative_to(ROOT))] = digest(path)
(OUT / "FalseControls.lean").write_bytes((HERE / "FalseControls.lean").read_bytes())
(OUT / "lean-toolchain").write_bytes((BASE / "integration/lean-toolchain").read_bytes())
for wrapper in ["bootloops-lean", "bootloops-lake"]:
    p = subprocess.run([str(ROOT / wrapper), "--version"], cwd=OUT, env=ENV, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
    (OUT / (wrapper + "-version.log")).write_text(p.stdout)
    assert p.returncode == 0, p.stdout
    record[wrapper + "_version"] = p.stdout.strip()

# Harness plants run before the production proof replay.
(OUT / "TrueControl.lean").write_text("import Std\nexample : (2 : Nat) + 3 = 5 := by decide\n")
(OUT / "FalseControl.lean").write_text("import Std\nexample : (2 : Nat) + 3 = 6 := by decide\n")
assert run("TrueControl").returncode == 0
p = run("FalseControl")
assert p.returncode != 0 and "is false" in p.stdout, p.stdout
record["controls"].update(known_true="ACCEPTED", known_false="REJECTED")
for n, _ in SPECS:
    p = run(n, True)
    assert p.returncode == 0 and not re.search(r"error:|sorryAx|declaration uses .sorry.", p.stdout), (n, p.stdout)
p = run("FalseControls")
assert p.returncode != 0 and p.stdout.count("is false") == 5, p.stdout
record["controls"]["five_pinned_false_claims"] = "REJECTED_5_OF_5"

modules = ", ".join("`" + n for n, _ in SPECS)
inventory = '''import Consumers
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : List Name := [MODULES]
  for mod in env.header.moduleNames do
    let path ← liftIO <| findOLean mod
    logInfo m!"PATH|{mod}|{path}"
  let ns := (env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)
  let ns := (ns.filter fun n =>
    match env.getModuleIdxFor? n with
    | some idx => modules.contains env.header.moduleNames[idx.toNat]!
    | none => false).eraseDups
  for n in ns do
    let some idx := env.getModuleIdxFor? n | throwError "missing module origin"
    let mod := env.header.moduleNames[idx.toNat]!
    logInfo m!"MODULE|{mod}|{n}"
  for n in ns do
    let axs ← collectAxioms n
    logInfo m!"MODAUDIT|{n}|{String.intercalate "," (axs.toList.map toString)}"
    for a in axs do
      unless a == `propext || a == `Quot.sound || a == `Classical.choice do
        throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
'''.replace("MODULES", modules)
(OUT / "ModuleInventory.lean").write_text(inventory)
p = run("ModuleInventory")
assert p.returncode == 0, p.stdout

def parse(s):
    origins = re.findall(r"^MODULE\|([^|]+)\|(.+)$", s, re.M)
    axioms = re.findall(r"^MODAUDIT\|([^|]+)\|([^\n]*)$", s, re.M)
    assert origins and len(origins) == len(axioms) == len(set(origins)), "incomplete/duplicate audit"
    assert {n for _, n in origins} == {n for n, _ in axioms}, "missing axiom declaration"
    assert {m for m, _ in origins} == {n for n, _ in SPECS}, "missing/extra source module"
    paths = dict(re.findall(r"^PATH\|([^|]+)\|(.+)$", s, re.M))
    for mod, rawpath in paths.items():
        path = Path(rawpath).resolve()
        if mod in {n for n, _ in SPECS}:
            assert path == OUT / (mod + ".olean"), "wrong local module origin: " + mod
        else:
            assert path.is_relative_to(ROOT / ".runtime/elan/toolchains"), "non-toolchain dependency: " + str(path)
    for mod, _ in SPECS:
        assert mod in paths, "missing source path: " + mod
    return origins, axioms, paths

origins, axioms, paths = parse(p.stdout)
for label, corrupted in [
    ("missing_axiom_record", re.sub(r"^MODAUDIT\|[^\n]+\n", "", p.stdout, count=1, flags=re.M)),
    ("wrong_module_path", re.sub(r"^PATH\|Restriction\|[^\n]+", "PATH|Restriction|/tmp/foreign.olean", p.stdout, flags=re.M)),
    ("wrong_module_origin", re.sub(r"^MODULE\|Restriction\|", "MODULE|ForeignModule|", p.stdout, count=1, flags=re.M)),
]:
    try:
        parse(corrupted)
    except AssertionError as err:
        record["controls"][label] = "CAUGHT: " + str(err)
    else:
        raise AssertionError("corruption survived: " + label)
record["module_origin_counts"] = {n: sum(mod == n for mod, _ in origins) for n, _ in SPECS}
record["module_origin_total"] = len(origins)
record["resolved_module_paths"] = paths
record["axiom_union_observed"] = sorted({x.strip() for _, xs in axioms for x in xs.split(",") if x.strip()})
assert set(record["axiom_union_observed"]) <= ALLOWED

# Isolated hostile module: never imported by the production proof chain.
(OUT / "PlantModel.lean").write_text("namespace HiddenRestrictionPlant\naxiom borrowed : False\nend HiddenRestrictionPlant\n")
assert run("PlantModel", True).returncode == 0
(OUT / "ModulePlantAudit.lean").write_text("import PlantModel\n" + inventory.replace("`Consumers]", "`Consumers, `PlantModel]"))
p = run("ModulePlantAudit")
assert p.returncode != 0 and "REJECT_CUSTOM_AXIOM|HiddenRestrictionPlant.borrowed|HiddenRestrictionPlant.borrowed" in p.stdout
record["controls"]["hidden_custom_axiom"] = "CAUGHT"
corrupt_source = OUT / "Restriction-corrupted.txt"
corrupt_source.write_bytes((OUT / "Restriction.lean").read_bytes() + b"\n-- deliberate source corruption\n")
assert digest(corrupt_source) != record["input_hashes"][str((HERE / "Restriction.lean").relative_to(ROOT))]
record["controls"]["source_byte_corruption"] = "CAUGHT"
for rel, sha in record["input_hashes"].items():
    assert digest(ROOT / rel) == sha, "source changed during replay: " + rel
for n, path in SPECS:
    assert digest(OUT / (n + ".lean")) == digest(path), "snapshot changed during replay: " + n
record.update(status="PASS_AUTHOR_KERNEL_REPLAY", forward_decomposition=True,
              reverse_reconstruction=True, exact_local_cost=True, proper_component_labels=True,
              minimal_embedding_transport=True, fresh_nonauthor_review=False,
              first_unfinished_graph_consumer=None)
record["module_inventory_sha256"] = digest(OUT / "ModuleInventory.log")
save()
summary = {k: record[k] for k in ["status", "grade", "forward_decomposition", "reverse_reconstruction",
           "module_origin_total", "module_origin_counts", "axiom_union_observed", "controls", "all_three_main_milestones"]}
summary["receipt"] = str(OUT.relative_to(ROOT))
(ROOT / "research/rmaf/results" / ("algorithm-universal233-restriction-" + stamp + ".json")).write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(summary, indent=2))
