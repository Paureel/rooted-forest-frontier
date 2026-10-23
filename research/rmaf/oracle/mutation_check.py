#!/usr/bin/env python3
"""Show the production control comparator can reject a planted bad expected k."""
import json
from pathlib import Path
import subprocess
import sys
from oracle import HERE, RESULTS, sha, write_json

fixture = json.loads((HERE/"controls.json").read_text())
fixture["optima"][2]["k"] = 1  # The frozen hand argument proves this value is false.
mutated_path = RESULTS/"oracle-deliberate-bad-expectation.json"
write_json(mutated_path,fixture)
process = subprocess.run([sys.executable,str(HERE/"oracle.py"),"controls","--fixture",str(mutated_path)],capture_output=True,text=True)
assert process.returncode != 0, "Comparator incorrectly accepted a known bad expectation"
assert "conflicting-triples" in process.stderr and "AssertionError" in process.stderr
receipt={"mutation":"conflicting-triples expected k changed from 2 to 1 on a separate copy","fixture_sha256":sha(HERE/"controls.json"),"mutated_fixture_sha256":sha(mutated_path),"production_command":["oracle.py","controls","--fixture",str(mutated_path.relative_to(HERE.parents[2]))],"returncode":process.returncode,"stdout":process.stdout,"stderr":process.stderr,"status":"deliberate-mismatch-rejected"}
write_json(RESULTS/"oracle-comparator-mutation.json",receipt)
print(json.dumps({"status":receipt["status"],"returncode":process.returncode}))
