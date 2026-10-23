#!/usr/bin/env python3
"""One-shot independent precontact calibration; never reads candidate evidence.
Known literal answers live in CONTROLS-v1.json, authored before this code.
This program is not a candidate source meter and does not certify itself.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import selectors
import shutil
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "CONTROLS-v1.json"
EXPECTED_FIXTURE_SHA = "ce569b07dae1cb212808eef204153553a6407f5715b30237249b42b5c9bc9b42"

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")

def trace_total(trace):
    nodes = {node["id"]: node for node in trace["nodes"]}
    if len(nodes) != len(trace["nodes"]):
        raise ValueError("execution IDs must be unique")
    active, visited = set(), []
    def visit(key):
        if key in active:
            raise ValueError("cyclic execution")
        if key in visited:
            raise ValueError("one execution ID reached twice; repeated physical calls need distinct IDs")
        active.add(key)
        node = nodes[key]
        if node["work"] < 0:
            raise ValueError("negative work")
        visited.append(key)
        result = node["work"]
        for child in node["children"]:
            result += visit(child)
        active.remove(key)
        return result
    result = visit(trace["root"])
    if set(visited) != set(nodes):
        raise ValueError("unreachable execution records")
    return result, len(visited)

def progress(edge):
    (parent_q, parent_size), (child_q, child_size) = edge
    return child_q < parent_q or (child_q == parent_q and child_size < parent_size)

def main():
    args = argparse.ArgumentParser()
    args.add_argument("--pilot", action="store_true")
    options = args.parse_args()
    if sha(FIXTURE) != EXPECTED_FIXTURE_SHA:
        raise RuntimeError("Frozen fixture hash changed")
    fixture = json.loads(FIXTURE.read_text())
    floor = fixture["limits"]["disk_floor_bytes"]
    if shutil.disk_usage(HERE).free < floor:
        raise RuntimeError("3 GiB free-disk floor violated before run")
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    out = HERE / "runs" / (("pilot-" if options.pilot else "full-") + stamp)
    out.mkdir(parents=True, exist_ok=False)
    start = time.monotonic()
    events = []
    record = {"utc": stamp, "phase": "PILOT" if options.pilot else "FULL", "status": "RUNNING", "fixture_sha256": sha(FIXTURE), "runner_sha256": sha(__file__), "python": sys.version, "python_executable": sys.executable, "pre_run_free_bytes": shutil.disk_usage(HERE).free, "candidate_contact": False}
    dump(out / "receipt.json", record)
    def case(name, actual, expected, kind="positive"):
        event = {"name": name, "kind": kind, "actual": actual, "expected": expected, "pass": actual == expected}
        events.append(event)
        with (out / "cases.jsonl").open("a") as stream:
            stream.write(json.dumps(event, sort_keys=True) + "\n")
        if not event["pass"]:
            raise AssertionError(name + ": actual did not equal frozen expected")
    def reject(name, observed, corrupt_claim):
        case(name, observed == corrupt_claim, False, "corruption")
    try:
        value, calls = trace_total(fixture["valid_trace"])
        case("literal-valid-trace", [value, calls], [fixture["valid_trace"]["expected_total"], fixture["valid_trace"]["expected_calls"]])
        if options.pilot:
            record.update(status="PILOT_PASSED", elapsed_seconds=time.monotonic()-start, positive_count=1, corruption_count=0)
            dump(out / "receipt.json", record)
            print("PILOT_PASSED 1/1 literal traces; no candidate contact")
            print(str(out))
            return
        v, calls = trace_total(fixture["duplicate_failed_trace"])
        case("literal-failed-duplicate-trace", [v,calls], [fixture["duplicate_failed_trace"]["expected_total"], fixture["duplicate_failed_trace"]["expected_calls"]])
        for key in ("drop_one_failed_leaf_claim", "drop_duplicate_expansion_claim", "drop_both_claim"):
            reject(key, v, fixture["duplicate_failed_trace"][key])
        rat = fixture["rational"]
        c = Fraction(*rat["c"])
        mass, gamma = 2/c+1/(c*c), 2/c+4/(c**4)
        case("retained-mass-literal", [mass.numerator,mass.denominator], rat["old_mass"])
        case("gamma-literal-and-range", [[gamma.numerator,gamma.denominator], 0 < gamma < 1], [rat["gamma"], True])
        reject("retained-mass-at-most-one", mass <= 1, True)
        reject("gamma-off-by-one-numerator", gamma, Fraction(rat["gamma"][0]+1, rat["gamma"][1]))
        prog = fixture["progress"]
        case("same-budget-strict-size", progress(prog["same_q_strict_size"]), True)
        case("budget-decrease-same-size", progress(prog["q_decrease_same_size"]), True)
        for key in ("unchanged_cycle", "same_q_growth", "budget_growth"):
            reject("invalid-progress-"+key, progress(prog[key]), True)
        coeff = fixture["coefficient"]
        cap = coeff["D"] * coeff["root_scaled_mass"]
        once = coeff["D"] * coeff["frontier_scaled_mass"]
        twice = once + once
        case("one-paid-coefficient-frontier", [cap,once,once <= cap], [coeff["expected_cap"], coeff["expected_once"], True])
        reject("repeated-depth-coefficient-fits", twice <= cap, True)
        if twice != coeff["expected_twice"]:
            raise AssertionError("twice-cost-literal changed")
        direct = fixture["direct"]
        direct_total = direct["wrapper_work"] + sum(direct["ordinary_callback_work"])
        case("empty-outer-trace-has-direct-callback", [direct_total,len(direct["ordinary_callback_work"]),len(direct["outer_forest_trace"])], [direct["expected_total"],direct["expected_callbacks"],0])
        reject("drop-direct-callback", direct_total, direct["drop_callback_claim"])
        sheet = fixture["source_sheet"]
        charged = ("query_generation", "query_check", "state_copy", "returned_payload_bits", "scalar_label_bits", "ordinary_callback")
        sheet_total = sum(sheet[key] for key in charged)
        case("complete-source-sheet", sheet_total, sheet["expected_total"])
        case("clean-returned-payload-cap", sheet["returned_payload_bits"] <= sheet["payload_cap_bits"], True)
        for key in charged[:-1]:
            reject("omit-"+key, sheet_total, sheet_total-sheet[key])
        reject("huge-returned-payload-cap", sheet["huge_payload_bits"] <= sheet["payload_cap_bits"], True)
        label_bits = len(("a"*sheet["label_string_length"]).encode("utf-8"))*8
        if label_bits != sheet["actual_utf8_label_bits"]:
            raise AssertionError("label-bit ground truth changed")
        reject("scalar-label-underbilling", label_bits <= sheet["claimed_label_bits"], True)
        null = fixture["null"]
        case("null-empty-work", sum(null["works"]), null["expected_total"])
        case("null-reinsert-component", sum(null["works"])+null["reinsert_work"], null["expected_reinsert_total"])
        positive_count = sum(e["kind"]=="positive" for e in events)
        corruption_count = sum(e["kind"]=="corruption" for e in events)
        if [positive_count,corruption_count] != [fixture["expected_counts"]["python_positive_cases"],fixture["expected_counts"]["python_corruption_catches"]]:
            raise AssertionError("fixed control denominator mismatch")
        runtime = HERE.parents[5] / ".runtime" / "elan" / "toolchains" / "leanprover--lean4---v4.35.0" / "bin" / "lean"
        if not runtime.is_file():
            raise RuntimeError("expected installed Lean binary unavailable: "+str(runtime))
        record["lean_binary"] = str(runtime)
        record["lean_binary_sha256"] = sha(runtime)
        lean_receipts = []
        names = [fixture["lean"]["positive"]] + fixture["lean"]["negative"]
        for name in names:
            source = HERE / name
            source_text = source.read_text()
            if re.search(r'\b(?:sorry|admit|native_decide)\b|\baxiom\s', source_text):
                raise AssertionError("forbidden proof syntax in "+name)
            if shutil.disk_usage(HERE).free < floor:
                raise RuntimeError("3 GiB free-disk floor violated before "+name)
            before = sha(source)
            command = [str(runtime), "-M"+str(fixture["limits"]["lean_megabytes"]), str(source)]
            process_start = time.monotonic()
            proc = subprocess.Popen(command,cwd=HERE,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
            selector = selectors.DefaultSelector()
            selector.register(proc.stdout,selectors.EVENT_READ)
            count, timed_out, overflow = 0, False, False
            chunks = []
            deadline = process_start + fixture["limits"]["initial_subprocess_seconds"]
            logpath = out/(name+".log.gz")
            with gzip.open(logpath,"wb") as logfile:
                while selector.get_map():
                    if time.monotonic() >= deadline:
                        timed_out = True
                        os.killpg(proc.pid,signal.SIGKILL)
                        break
                    for key,_ in selector.select(timeout=min(0.2,max(0,deadline-time.monotonic()))):
                        chunk = os.read(key.fd,8192)
                        if not chunk:
                            selector.unregister(key.fileobj)
                            continue
                        count += len(chunk)
                        remaining = fixture["limits"]["max_log_bytes"] - sum(len(item) for item in chunks)
                        kept = chunk[:max(remaining,0)]
                        chunks.append(kept)
                        logfile.write(kept)
                        if count > fixture["limits"]["max_log_bytes"]:
                            overflow = True
                            os.killpg(proc.pid,signal.SIGKILL)
                            break
                    if overflow:
                        break
            proc.wait(timeout=2)
            selector.close()
            proc.stdout.close()
            logtext = b"".join(chunks).decode("utf-8",errors="replace")
            after = sha(source)
            expected_positive = name == fixture["lean"]["positive"]
            passed = not timed_out and not overflow and before==after and ((proc.returncode==0) if expected_positive else (proc.returncode!=0 and "decide" in logtext and "error:" in logtext))
            if expected_positive:
                axiom_reports = re.findall(r"'SolIndependentControls\.[^']+' (?:does not depend on any axioms|depends on axioms: \[[^]]*\])",logtext)
                passed = passed and len(axiom_reports)==fixture["expected_counts"]["lean_positive_theorems"]
                axiom_names = set(re.findall(r"\b(?:propext|Classical.choice|Quot.sound|sorryAx|Lean.ofReduceBool|Lean.trustCompiler)\b",logtext))
                passed = passed and axiom_names <= {"propext","Classical.choice","Quot.sound"}
            else:
                axiom_reports, axiom_names = [],set()
            receipt = {"source":name,"source_sha256_before":before,"source_sha256_after":after,"argv":command,"cwd":str(HERE),"exit_code":proc.returncode,"elapsed_seconds":time.monotonic()-process_start,"timed_out":timed_out,"log_overflow":overflow,"uncompressed_log_bytes":count,"log":logpath.name,"log_sha256":sha(logpath),"expected_positive":expected_positive,"axiom_reports":axiom_reports,"recognized_axiom_names":sorted(axiom_names),"pass":passed}
            lean_receipts.append(receipt)
            dump(out/(name+".receipt.json"),receipt)
            if not passed:
                raise AssertionError("Lean control failed readiness requirements: "+name)
        record.update(status="CALIBRATION_PASSED",elapsed_seconds=time.monotonic()-start,positive_count=positive_count,corruption_count=corruption_count,lean_receipts=lean_receipts,post_run_free_bytes=shutil.disk_usage(HERE).free,scope="Readiness only; all candidate/base/main/novelty acceptance OPEN")
        dump(out/"receipt.json",record)
        print("CALIBRATION_PASSED Python positives 12/12; corruption catches 17/17")
        print("Lean positive theorem axiom reports 12/12; false propositions rejected 3/3")
        print("No candidate contact. Runtime/base/main/novelty OPEN.")
        print(str(out))
    except BaseException as error:
        record.update(status="FAILED",elapsed_seconds=time.monotonic()-start,error=repr(error),events_completed=len(events))
        dump(out/"receipt.json",record)
        print("FAILED retained receipt: "+str(out),file=sys.stderr)
        raise

if __name__ == "__main__":
    main()
