#!/usr/bin/env python3
"""One-shot outer gate for the independently constructed finite graph evaluator.

The numeric-blind instrument is a separate byte-pinned copy. Its acceptance of
known wrong numbers must make this unchanged outer gate refuse it.
"""
import argparse
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
CONTROL_PATH = HERE.parent / "controls.json"
HOSTILE_PATH = HERE / "hostile-controls.json"
NUMERIC_FIELDS = ("parent_count", "parent_cost", "left_count", "right_count", "left_cost", "right_cost", "toll")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def save(path, data):
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def pin_check():
    pin = json.loads((HERE / "PHASE1-SOURCE-PIN.json").read_text())
    rows = []
    for filename, expected in pin["sha256"].items():
        path = ROOT / filename
        actual = digest(path)
        rows.append({"path": filename, "expected": expected, "actual": actual, "match": actual == expected})
    if not all(row["match"] for row in rows):
        raise RuntimeError("source pin drift before evaluation")
    return rows


def trial(module, data, hostile, pilot=False):
    started = time.perf_counter()
    rows = []
    bases = {p["id"]: p for p in data["positives"]}
    positives = data["positives"][:1] if pilot else data["positives"]
    wrong_numbers = data["wrong_numbers"][:1] if pilot else data["wrong_numbers"]
    for p in positives:
        value = module.evaluate(p)
        comparison = module.compare_claim(value["summary"], p["expected"])
        rows.append({"category": "positive", "id": p["id"], "pass": comparison["accepted"],
                     "evaluation": value, "comparison": comparison})
    if not pilot:
        for m in data["malformed"]:
            bad = deepcopy(bases[m["base"]])
            bad.update(deepcopy(m["replace"]))
            error = None
            try:
                module.validate_family(bad)
            except module.InvalidFamily as e:
                error = str(e)
            rows.append({"category": "malformed", "id": m["id"], "pass": error is not None,
                         "rejection": error, "input": bad})
    for m in wrong_numbers:
        p = bases[m["base"]]
        value = module.evaluate(p)
        clean = deepcopy(p["expected"])
        clean[m["field"]] = m["correct"]
        bad = deepcopy(clean)
        bad[m["field"]] = m["wrong"]
        clean_comparison = module.compare_claim(value["summary"], clean)
        bad_comparison = module.compare_claim(value["summary"], bad)
        rows.append({"category": "wrong_number", "id": m["id"],
                     "pass": clean_comparison["accepted"] and not bad_comparison["accepted"],
                     "field": m["field"], "actual": value["summary"][m["field"]],
                     "correct": m["correct"], "wrong": m["wrong"],
                     "clean": clean_comparison, "corrupt": bad_comparison})
    if not pilot:
        for m in data["corruptions"]:
            p = bases[m["base"]]
            value = module.evaluate(p)
            clean = deepcopy(p["expected"])
            clean[m["field"]] = m["correct"]
            bad = deepcopy(clean)
            bad[m["field"]] = m["wrong"]
            clean_comparison = module.compare_claim(value["summary"], clean)
            bad_comparison = module.compare_claim(value["summary"], bad)
            rows.append({"category": "corruption", "id": m["id"],
                         "pass": clean_comparison["accepted"] and not bad_comparison["accepted"],
                         "clean": clean_comparison, "corrupt": bad_comparison})
        for p in data["outside_premise"]:
            parent_validity = module.validate_family(p)
            live = [module.live_indices(p, side) for side in (0, 1)]
            premise = module.open_branch_live(p)
            children = [module.restrict_child(p, side) for side in (0, 1)]
            child_validities = [module.validate_family(c) for c in children]
            refused = False
            try:
                module.evaluate(p)
            except module.OutsidePremise:
                refused = True
            checks = {
                "parent_valid": parent_validity["valid"] == p["expected_family_valid"],
                "premise": premise == p["expected_open_branch_live"],
                "left_live": set(live[0]) == set(p["expected_live_left_indices"]),
                "right_live": set(live[1]) == set(p["expected_live_right_indices"]),
                "no_forbidden_left_boundary": children[0]["boundary"] != p["forbidden_child_boundary"],
                "outside_premise_refused": refused,
            }
            rows.append({"category": "outside_premise", "id": p["id"], "pass": all(checks.values()),
                         "checks": checks, "parent_validity": parent_validity,
                         "live_indices": live, "open_branch_live": premise,
                         "children": children, "child_validities": child_validities})
        for p in hostile["cases"]:
            value = module.evaluate(p)
            bad = deepcopy(p["expected"])
            bad.update(deepcopy(p["corrupt_patch"]))
            clean_comparison = module.compare_claim(value["summary"], p["expected"])
            bad_comparison = module.compare_claim(value["summary"], bad)
            corrupted_children = []
            for side, prefix in enumerate(("left", "right")):
                region = bad[prefix + "_regions"]
                child = {"tree": p["tree"][side], "indices": list(region), "regions": region,
                         "boundary": bad[prefix + "_boundary"]}
                corrupted_children.append(module.validate_family(child))
            unchanged_numbers = all(bad[f] == value["summary"][f] for f in NUMERIC_FIELDS)
            checks = {"clean_accepted": clean_comparison["accepted"],
                      "corruption_rejected": not bad_comparison["accepted"],
                      "corrupt_children_valid": all(c["valid"] for c in corrupted_children),
                      "all_numbers_unchanged": unchanged_numbers}
            rows.append({"category": "hostile", "id": p["id"], "pass": all(checks.values()),
                         "checks": checks, "evaluation": value, "corrupt_claim": bad,
                         "corrupt_child_validity": corrupted_children,
                         "clean": clean_comparison, "corrupt": bad_comparison})
    observed = {cat: sum(r["category"] == cat for r in rows) for cat in
                ("positive", "malformed", "wrong_number", "corruption", "outside_premise", "hostile")}
    expected = ({"positive": 1, "malformed": 0, "wrong_number": 1, "corruption": 0,
                 "outside_premise": 0, "hostile": 0} if pilot else
                {"positive": 8, "malformed": 4, "wrong_number": 5, "corruption": 3,
                 "outside_premise": 1, "hostile": 2})
    denominators = observed == expected
    return {"started_utc": datetime.now(timezone.utc).isoformat(), "elapsed_seconds": time.perf_counter() - started,
            "denominators_ok": denominators, "expected_denominators": expected,
            "observed_denominators": observed, "outer_gate_accepts": denominators and all(r["pass"] for r in rows),
            "passing_rows": sum(r["pass"] for r in rows), "total_rows": len(rows), "rows": rows}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True)
    parser.add_argument("--pilot", action="store_true")
    args = parser.parse_args()
    output = Path(args.output)
    output.mkdir(parents=True, exist_ok=False)
    pins = pin_check()
    controls = json.loads(CONTROL_PATH.read_text())
    hostile = json.loads(HOSTILE_PATH.read_text())
    original = load_module(HERE / "finite_graph.py", "fresh_original")
    regular = trial(original, controls, hostile, args.pilot)
    save(output / "original.json", regular)
    if args.pilot:
        verdict = regular["outer_gate_accepts"]
        report = {"stage": "pilot", "source_pins": pins, "passed": verdict,
                  "elapsed_seconds": regular["elapsed_seconds"], "rows": regular["total_rows"]}
    else:
        mutant = load_module(HERE / "finite_graph_numeric_blind.py", "fresh_numeric_blind")
        broken = trial(mutant, controls, hostile)
        save(output / "numeric-blind.json", broken)
        numeric_rows = [r for r in broken["rows"] if r["category"] == "wrong_number"]
        escapes = [r["id"] for r in numeric_rows if r["clean"]["accepted"] and r["corrupt"]["accepted"]]
        plant_checks = {"all_five_wrong_numbers_escape": len(escapes) == 5,
                        "outer_gate_rejects_numeric_blind": not broken["outer_gate_accepts"],
                        "mutant_denominators_complete": broken["denominators_ok"],
                        "other_mutant_rows_pass": all(r["pass"] for r in broken["rows"] if r["category"] != "wrong_number")}
        verdict = regular["outer_gate_accepts"] and all(plant_checks.values())
        report = {"stage": "full", "source_pins": pins, "passed": verdict,
                  "original_outer_gate_accepts": regular["outer_gate_accepts"],
                  "original_passes": regular["passing_rows"], "original_denominator": regular["total_rows"],
                  "original_denominators": regular["observed_denominators"],
                  "original_elapsed_seconds": regular["elapsed_seconds"],
                  "numeric_blind_outer_gate_accepts": broken["outer_gate_accepts"],
                  "numeric_blind_escapes": escapes, "numeric_blind_elapsed_seconds": broken["elapsed_seconds"],
                  "plant_checks": plant_checks}
    report["source_pins_after"] = pin_check()
    save(output / "summary.json", report)
    print(json.dumps({k: v for k, v in report.items() if not k.startswith("source_pins")}, sort_keys=True))
    if not verdict:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
