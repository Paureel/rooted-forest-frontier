#!/usr/bin/env python3
"""One-shot additive local arithmetic calibration, intentionally not a framework.

No project verifier, source counter, candidate executable, or Phase A script is
imported. Manual expectations are in ARITHMETIC-PREREGISTRATION-v1.md.
"""
import argparse
import json
from pathlib import Path
import platform
import sys


def width(n):
    if not isinstance(n, int) or n < 0:
        raise ValueError("unsigned integer required")
    return max(1, n.bit_length())


def emit_bill(m, v, omit_value_occurrence=False):
    post = m + 1
    write = 1 + width(m) + width(m) + width(v) + width(post)
    if not omit_value_occurrence:
        write += width(v)
    constant_one = 1 + width(1)
    addition = 1 + width(m) + width(1) + width(post)
    return write + constant_one + addition


def expanded(m, v):
    return 5 + 3 * width(m) + 2 * width(v) + 2 * width(m + 1)


def scan_meter(debits, outcomes, position=0):
    if position == len(outcomes):
        return {"work": 2, "trials": 0, "selected": False}
    if outcomes[position]:
        return {"work": debits[position] + 12, "trials": 1, "selected": True}
    tail = scan_meter(debits, outcomes, position + 1)
    return {"work": debits[position] + tail["work"] + 12,
            "trials": tail["trials"] + 1, "selected": tail["selected"]}


def optimize_meter(debits):
    scan = scan_meter(debits, (False, False, True))
    if not scan["selected"]:
        raise AssertionError("constructed success was not reached")
    finish_work = 11 + 12
    return {"scan_work": scan["work"], "finish_work": finish_work,
            "complete_work": 7 + scan["work"] + finish_work + 8,
            "trials": scan["trials"], "recoveries": 1}


class Mismatch(Exception):
    def __init__(self, code, expected, observed):
        self.diagnostic = {"code": code, "expected": expected, "observed": observed}


def require(code, expected, observed):
    if expected != observed:
        raise Mismatch(code, expected, observed)


def clean_cases():
    points = ((0, 0), (3, 1), (8, 8))
    observed = {"emissions": [emit_bill(m, v) for m, v in points],
                "expanded": [expanded(m, v) for m, v in points],
                "empty_sum": sum(emit_bill(m, v) for m, v in ())}
    require("C1_FEE", {"emissions": [12, 19, 33], "expanded": [12, 19, 33], "empty_sum": 0}, observed)
    opt = optimize_meter((3, 5, 7))
    require("C2_OPTIMIZER", {"scan_work": 51, "finish_work": 23,
                              "complete_work": 89, "trials": 3, "recoveries": 1}, opt)
    return [{"id": "C1", "status": "MATCH", "observed": observed},
            {"id": "C2", "status": "MATCH", "observed": opt}]


def corrupt_cases():
    results = []
    cases = (("N1", "WRITE_VALUE_MULTIPLICITY", 33, emit_bill(8, 8, True), 29),
             ("N2", "FAILED_TRIAL_DEBITS_OMITTED", 89,
              optimize_meter((0, 0, 7))["complete_work"], 81))
    for identity, code, good, bad, expected_bad in cases:
        try:
            require(code, good, bad)
        except Mismatch as error:
            require("WRONG_DIAGNOSTIC", {"code": code, "expected": good, "observed": expected_bad}, error.diagnostic)
            results.append({"id": identity, "status": "CAUGHT", "diagnostic": error.diagnostic})
        else:
            raise Mismatch("CORRUPTION_SURVIVED", "caught", identity)
    return results


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("positive", "corrupted"))
    parser.add_argument("--result", required=True, type=Path)
    args = parser.parse_args()
    if args.result.exists():
        raise FileExistsError("preserve existing evidence")
    result = {"mode": args.mode, "scope": "local exact calibration only; no candidate verdict",
              "runtime": {"implementation": platform.python_implementation(),
                          "version": platform.python_version(), "executable": sys.executable}}
    code = 1
    try:
        result["cases"] = clean_cases() if args.mode == "positive" else corrupt_cases()
        require("DENOMINATOR", 2, len(result["cases"]))
        result["status"] = "TWO_CLEAN_MATCHES" if args.mode == "positive" else "TWO_CORRUPTIONS_CAUGHT"
        code = 0 if args.mode == "positive" else 23
    except Exception as error:
        result["status"] = "UNEXPECTED_CALIBRATION_FAILURE"
        result["error"] = getattr(error, "diagnostic", {"type": type(error).__name__, "message": str(error)})
    result["exit_code"] = code
    args.result.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    for case in result.get("cases", []):
        print(json.dumps(case, sort_keys=True))
    print(json.dumps({key: value for key, value in result.items() if key != "cases"}, sort_keys=True))
    return code


if __name__ == "__main__":
    sys.exit(main())
