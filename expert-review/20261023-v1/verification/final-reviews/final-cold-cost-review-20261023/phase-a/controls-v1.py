#!/usr/bin/env python3
"""One-shot cold Phase A calibration; deliberately not a registered framework.

Own synthetic construction only. Expected constants were written manually in
PREREGISTRATION-v1.md before this script was run. This does not import a project
verifier or the unreleased candidate. Python execution costs are not the toy bill.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
from fractions import Fraction
import json
from pathlib import Path
import platform
import sys


def bits(value: int) -> int:
    if not isinstance(value, int) or value < 0:
        raise ValueError("unsigned integer required")
    return max(1, value.bit_length())


def fee(operands: tuple[int, ...]) -> int:
    return 1 + sum(bits(value) for value in operands)


class Trace:
    def __init__(self) -> None:
        self.heap: dict[int, int] = {}
        self.events: list[dict] = []

    def emit(self, op: str, operands: tuple[int, ...], owner: str,
             stage: str, occurrence: int | None = None,
             address_positions: tuple[int, ...] = ()) -> None:
        self.events.append({
            "ordinal": len(self.events) + 1, "op": op,
            "operands": list(operands), "owner": owner, "stage": stage,
            "occurrence": occurrence, "fee": fee(operands),
            "address_bit_fee": sum(bits(operands[i]) for i in address_positions),
        })

    def allocate(self, value: int, owner: str, stage: str,
                 occurrence: int | None = None) -> int:
        address = len(self.heap) + 1
        self.heap[address] = value
        self.emit("ALLOC", (address, value), owner, stage, occurrence, (0,))
        return address

    def read(self, address: int, owner: str, stage: str,
             occurrence: int | None = None) -> int:
        value = self.heap[address]
        self.emit("READ", (address, value), owner, stage, occurrence, (0,))
        return value


def toy_trace() -> tuple[Trace, list[dict], list[int]]:
    trace = Trace()
    source = [trace.allocate(v, "initialization", "init") for v in (7, 9)]
    stored = []
    for occurrence in (1, 2, 3):
        trace.emit("PRODUCE", (occurrence,), "producer", "eager", occurrence)
        copied = []
        for original_address in source:
            value = trace.read(original_address, "copy", "eager", occurrence)
            copied.append(trace.allocate(value, "copy", "eager", occurrence))
        metadata = trace.allocate(occurrence, "metadata", "eager", occurrence)
        stored.append({"id": occurrence, "copied": copied, "metadata": metadata})
    for occurrence in (3, 1, 2):
        item = stored[occurrence - 1]
        observed_id = trace.read(item["metadata"], "metadata", "consume", occurrence)
        flag = int(observed_id == 1)
        trace.emit("DECIDE", (observed_id, flag), "decision", "consume", occurrence)
    return trace, stored, source


def summary(trace: Trace, stored: list[dict], source: list[int]) -> dict:
    events = trace.events
    decisions = [e for e in events if e["op"] == "DECIDE"]
    refused = {e["occurrence"] for e in decisions if e["operands"][1] == 0}
    width = bits(max(trace.heap, default=0))
    max_operands = max((len(e["operands"]) for e in events), default=0)
    max_operand_width = max((bits(v) for e in events for v in e["operands"]), default=1)
    return {
        "bill": sum(e["fee"] for e in events), "events": len(events),
        "retained_cells": len(trace.heap),
        "source_cells": len(source),
        "copied_cells": sum(e["op"] == "ALLOC" and e["owner"] == "copy" for e in events),
        "metadata_cells": sum(e["op"] == "ALLOC" and e["owner"] == "metadata" for e in events),
        "produced": sum(e["op"] == "PRODUCE" for e in events),
        "visited": len(decisions),
        "distinct_payloads": len({tuple(trace.heap[a] for a in item["copied"]) for item in stored}),
        "accepted": sum(e["operands"][1] for e in decisions),
        "refused": len(refused),
        "refused_eager_bill": sum(e["fee"] for e in events if e["stage"] == "eager" and e["occurrence"] in refused),
        "address_bit_fees": sum(e["address_bit_fee"] for e in events),
        "max_address_width": width,
        "structural_allocation_bound": len(source) + len(stored) * (len(source) + 1),
        "coarse_fee_bound": len(events) * (1 + max_operands * max_operand_width),
        "owner_bills": {owner: sum(e["fee"] for e in events if e["owner"] == owner)
                        for owner in ("initialization", "producer", "copy", "metadata", "decision")},
        "stored_order": [item["id"] for item in stored],
        "dynamic_order": [e["occurrence"] for e in decisions],
    }


def cycle(graph: dict[str, list[str]]) -> list[str] | None:
    active: list[str] = []
    finished: set[str] = set()

    def visit(node: str) -> list[str] | None:
        if node in active:
            return active[active.index(node):] + [node]
        if node in finished:
            return None
        if node not in graph:
            raise ValueError(f"unprovided dependency {node}")
        active.append(node)
        for dependency in sorted(graph[node]):
            found = visit(dependency)
            if found:
                return found
        active.pop()
        finished.add(node)
        return None

    for node in sorted(graph):
        found = visit(node)
        if found:
            return found
    return None


def optimizer(trials: tuple[int, ...] = (3, 5, 7), recoveries: int = 1) -> dict:
    mass = sum((1, 2, 3))
    bill = 2
    for trial_bill in trials:
        bill += trial_bill
    for _ in range(recoveries):
        bill += 11
    return {"bill": bill, "trial_count": len(trials), "recoveries": recoveries,
            "mass": mass, "mass_bound": 4 * (mass + 1)}


class Mismatch(Exception):
    def __init__(self, diagnostic: dict):
        self.diagnostic = diagnostic


def equal(code: str, expected, observed) -> None:
    if expected != observed:
        raise Mismatch({"code": code, "expected": expected, "observed": observed})


def inequality(code: str, left: Fraction | int, right: Fraction | int) -> None:
    if left > right:
        raise Mismatch({"code": code, "lhs": str(left), "rhs": str(right),
                        "residual": str(left - right)})


EXPECTED_TRACE = {
    "bill": 151, "events": 26, "retained_cells": 11, "source_cells": 2,
    "copied_cells": 6, "metadata_cells": 3, "produced": 3, "visited": 3,
    "distinct_payloads": 1, "accepted": 1, "refused": 2, "refused_eager_bill": 76,
    "address_bit_fees": 53, "max_address_width": 4,
    "structural_allocation_bound": 11, "coarse_fee_bound": 234,
    "owner_bills": {"initialization": 12, "producer": 8, "copy": 82,
                    "metadata": 38, "decision": 11},
    "stored_order": [1, 2, 3], "dynamic_order": [3, 1, 2],
}
GRAPH = {"allocation": ["inputs"], "width": ["allocation"],
         "operand": ["inputs"], "fee": ["width", "operand"],
         "desired_bill": ["fee"], "inputs": []}


def positives(trace: Trace, stored: list[dict], source: list[int]) -> list[dict]:
    results = []
    empty = summary(Trace(), [], [])
    null = {key: empty[key] for key in ("bill", "events", "retained_cells", "address_bit_fees", "max_address_width")}
    equal("P0_NULL", {"bill": 0, "events": 0, "retained_cells": 0,
                      "address_bit_fees": 0, "max_address_width": 1}, null)
    results.append({"id": "P0", "status": "MATCH", "observed": null})
    measured = summary(trace, stored, source)
    equal("P1_TRACE", EXPECTED_TRACE, measured)
    inequality("P1_FEE_ENVELOPE", measured["bill"], measured["coarse_fee_bound"])
    equal("P1_ALLOCATION_BEFORE_WIDTH", measured["structural_allocation_bound"], measured["retained_cells"])
    results.append({"id": "P1", "status": "MATCH", "observed": measured})
    arithmetic = {"full_fee": fee((8, 8, 64)), "dedup_fee": fee((8, 64))}
    equal("P2_MULTIPLICITY", {"full_fee": 16, "dedup_fee": 12}, arithmetic)
    results.append({"id": "P2", "status": "MATCH", "observed": arithmetic})
    equal("P3_DEPENDENCY", None, cycle(GRAPH))
    results.append({"id": "P3", "status": "MATCH", "observed": "acyclic"})
    opt = optimizer()
    equal("P4_COMPOSITION", {"bill": 28, "trial_count": 3, "recoveries": 1,
                             "mass": 6, "mass_bound": 28}, opt)
    results.append({"id": "P4", "status": "MATCH", "observed": opt})
    r = Fraction(233, 100)
    exponent_bound = 2 * r**2
    substituted = 4 * (exponent_bound + 1)
    absorbed = 4 * 3 * r**2
    raised = 4 * 3 * r**3
    rationals = {"source_bound": str(exponent_bound), "substituted": str(substituted),
                 "absorbed": str(absorbed), "raised": str(raised)}
    equal("P5_EXACT_RATIONALS", {"source_bound": "54289/5000", "substituted": "59289/1250",
                                "absorbed": "162867/2500", "raised": "37948011/250000"}, rationals)
    for tag, left, right in (("source", 6, exponent_bound), ("bill", 28, 4 * 7),
                             ("substitute", 28, substituted), ("absorb", substituted, absorbed),
                             ("raise", absorbed, raised)):
        inequality("P5_" + tag, left, right)
    results.append({"id": "P5", "status": "MATCH", "observed": rationals, "inequalities": 5})
    equal("POSITIVE_DENOMINATOR", 6, len(results))
    return results


def corruptions(trace: Trace, stored: list[dict], source: list[int]) -> list[dict]:
    results = []

    def catch(case: str, call, expected: dict) -> None:
        try:
            call()
        except Mismatch as found:
            equal("WRONG_NEGATIVE_DIAGNOSTIC_" + case, expected, found.diagnostic)
            results.append({"id": case, "status": "CAUGHT", "diagnostic": found.diagnostic})
        else:
            raise Mismatch({"code": "CORRUPTION_SURVIVED", "id": case})

    collapsed = deepcopy(trace)
    collapsed.events = [e for e in collapsed.events if not
                        (e["op"] == "ALLOC" and e["owner"] == "copy" and e["occurrence"] in (2, 3))]
    catch("N1", lambda: equal("DUPLICATE_COPY_UNDERCOUNT", 6, summary(collapsed, stored, source)["copied_cells"]),
          {"code": "DUPLICATE_COPY_UNDERCOUNT", "expected": 6, "observed": 2})
    eager_omitted = deepcopy(trace)
    eager_omitted.events = [e for e in eager_omitted.events if not (e["stage"] == "eager" and e["occurrence"] in (2, 3))]
    catch("N2", lambda: equal("EAGER_REFUSED_WORK_OMITTED", 151, summary(eager_omitted, stored, source)["bill"]),
          {"code": "EAGER_REFUSED_WORK_OMITTED", "expected": 151, "observed": 75})
    metadata_omitted = deepcopy(trace)
    metadata_omitted.events = [e for e in metadata_omitted.events if not (e["op"] == "ALLOC" and e["owner"] == "metadata")]
    catch("N3", lambda: equal("METADATA_ALLOCATION_OMITTED", 3, summary(metadata_omitted, stored, source)["metadata_cells"]),
          {"code": "METADATA_ALLOCATION_OMITTED", "expected": 3, "observed": 0})
    measured = summary(trace, stored, source)
    catch("N4", lambda: equal("RETAINED_CELLS_CONFUSED_WITH_WIDTH", 11, measured["max_address_width"]),
          {"code": "RETAINED_CELLS_CONFUSED_WITH_WIDTH", "expected": 11, "observed": 4})
    catch("N5", lambda: equal("ARITHMETIC_OPERAND_MULTIPLICITY", 16, fee((8, 64))),
          {"code": "ARITHMETIC_OPERAND_MULTIPLICITY", "expected": 16, "observed": 12})
    circular = deepcopy(GRAPH)
    circular["allocation"] = ["desired_bill"]
    cycle_found = cycle(circular)
    catch("N6", lambda: equal("CIRCULAR_WIDTH_DEPENDENCY", "acyclic", cycle_found),
          {"code": "CIRCULAR_WIDTH_DEPENDENCY", "expected": "acyclic",
           "observed": ["allocation", "desired_bill", "fee", "width", "allocation"]})
    catch("N7", lambda: equal("OPTIMIZER_FAILED_TRIALS_OMITTED", 28, optimizer((7,))["bill"]),
          {"code": "OPTIMIZER_FAILED_TRIALS_OMITTED", "expected": 28, "observed": 20})
    catch("N8", lambda: equal("RECOVERY_MULTIPLICITY", 1, optimizer(recoveries=2)["recoveries"]),
          {"code": "RECOVERY_MULTIPLICITY", "expected": 1, "observed": 2})
    catch("N9", lambda: inequality("INEQUALITY_FALSE", 28, 4 * 6),
          {"code": "INEQUALITY_FALSE", "lhs": "28", "rhs": "24", "residual": "4"})
    catch("N10", lambda: inequality("SOURCE_BOUND_FALSE", 6, 1 * Fraction(2)**2),
          {"code": "SOURCE_BOUND_FALSE", "lhs": "6", "rhs": "4", "residual": "2"})
    equal("NEGATIVE_DENOMINATOR", 10, len(results))
    return results


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("positive", "corrupted"))
    parser.add_argument("--result", type=Path, required=True)
    args = parser.parse_args()
    if args.result.exists():
        raise FileExistsError("refuse to overwrite any evidence")
    trace, stored, source = toy_trace()
    output = {"mode": args.mode, "scope": "synthetic calibration only; no candidate verdict",
              "runtime": {"implementation": platform.python_implementation(),
                          "version": platform.python_version(), "executable": sys.executable},
              "engine_qualification": "shared BootLoops Python integer/Fraction engine; no external/kernel credit"}
    code = 1
    try:
        if args.mode == "positive":
            output["cases"] = positives(trace, stored, source)
            output["trace"] = trace.events
            output["status"] = "SIX_POSITIVES_MATCHED"
            code = 0
        else:
            output["cases"] = corruptions(trace, stored, source)
            output["status"] = "TEN_CORRUPTIONS_CAUGHT_EXPECTED_FAILURE_CHILD"
            code = 23
    except Exception as error:
        output["status"] = "UNEXPECTED_CONTROL_FAILURE"
        output["error"] = getattr(error, "diagnostic", {"type": type(error).__name__, "message": str(error)})
    output["exit_code"] = code
    args.result.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    for case in output.get("cases", []):
        print(json.dumps(case, sort_keys=True))
    if "error" in output:
        print(json.dumps(output["error"], sort_keys=True))
    print(json.dumps({"status": output["status"], "count": len(output.get("cases", [])),
                      "expected": 6 if args.mode == "positive" else 10, "exit_code": code}, sort_keys=True))
    return code


if __name__ == "__main__":
    sys.exit(main())
