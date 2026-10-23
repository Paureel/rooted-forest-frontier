#!/usr/bin/env python3
"""Replay registered result-file corruptions through the production comparator."""
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys

from edge_cut import BASE, WORK, write_json


if __name__ == "__main__":
    source = json.loads((WORK / "results/oracle-corpus.json").read_text())
    source["batches"] = [batch for batch in source["batches"] if batch["n"] == 3]
    rows = []
    for name in ("clean", "wrong-k", "wrong-optimum-partition", "missing-pair"):
        data = deepcopy(source)
        cases = data["batches"][0]["cases"]
        if name == "wrong-k":
            cases[0]["k"] += 1
        elif name == "wrong-optimum-partition":
            cases[0]["forests"] = [[]]
        elif name == "missing-pair":
            cases.pop()
        input_path = BASE / "plants" / (name + ".json")
        output_path = WORK / "results" / ("verification-plant-" + name + ".json")
        write_json(input_path, data)
        process = subprocess.run([sys.executable, str(BASE / "compare_results.py"),
             "--oracle", str(input_path), "--output", str(output_path), "--plant"],
             capture_output=True, text=True)
        expected = 0 if name == "clean" else 1
        if process.returncode != expected:
            raise AssertionError(f"plant {name} returned {process.returncode}, expected {expected}: {process.stdout} {process.stderr}")
        rows.append({"id": name, "expected_exit": expected, "observed_exit": process.returncode,
                     "stdout": process.stdout.strip(), "stderr": process.stderr.strip(),
                     "evidence": str(output_path.relative_to(WORK.parent.parent))})
    write_json(WORK / "results/verification-plants.json", {"rows": rows, "controls_executed": len(rows),
        "status": "all registered controls observed", "scope": "Comparator plumbing, not mathematical correctness."})
    print(json.dumps({"controls_executed": len(rows), "status": "clean twin accepted; three isolated corruptions rejected"}))
