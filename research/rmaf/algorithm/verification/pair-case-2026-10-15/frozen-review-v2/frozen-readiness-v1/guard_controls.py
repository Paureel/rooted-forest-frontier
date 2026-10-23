#!/usr/bin/env python3
"""One-shot guard controls; loads only own frozen independent instrument."""
import importlib.util
import json
import hashlib
from pathlib import Path
import sys

source, spec_path, output = map(Path, sys.argv[1:])
module_spec=importlib.util.spec_from_file_location("own_frozen_paircase",source)
m=importlib.util.module_from_spec(module_spec)
module_spec.loader.exec_module(m)
spec=json.loads(spec_path.read_text())
t=m.Original(spec["tree"]); a=spec["A"]; b=spec["B"]; e=tuple(spec["edge"])
c=m.Checks(); r=m.clear_edge(t,a,b,e); rs=m.clear_edge(t,b,a,e)
for name,actual,expected in [
    ("original_descendant_color",r["D"],spec["expected_D"]),
    ("four_sector_contents",r["sectors"],spec["expected_sectors"]),
    ("four_sectors",r["four_sectors"],True),
    ("whole_A_clear",r["mutual_A"],True),
    ("whole_B_not_clear",r["mutual_B"],False),
    ("one_parent_insufficient",r["eligible"],False),
    ("swapped_whole_A_not_clear",rs["mutual_A"],False),
    ("swapped_whole_B_clear",rs["mutual_B"],True),
    ("swapped_one_parent_insufficient",rs["eligible"],False),
    ("actual_A_two_regions",len(t.occupied(spec["shared_original_vertex"],a)),2),
    ("actual_B_three_regions",len(t.occupied(spec["shared_original_vertex"],b)),3),
    ("wrong_orientation_refused",m.clear_edge(t,a,b,tuple(spec["wrong_orientation"]))["eligible"],False),
    ("empty_sector_refused",m.clear_edge(t,a,b,tuple(spec["leaf_edge"]))["four_sectors"],False),
    ("suppressed_edge_not_original",tuple(spec["suppressed_edge"]) in m.Original(spec["suppressed_tree"]).edges,False)
]: c.equal(name,actual,expected)
result={"verdict":"BOUNDED-CONTROLS-PASSED","instrument_sha256":hashlib.sha256(source.read_bytes()).hexdigest(),
    "controls_source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    "spec_sha256":hashlib.sha256(spec_path.read_bytes()).hexdigest(),"control_denominator":len(c.rows),
    "checks":c.rows,"actual_guard_values":r,"swapped_guard_values":rs,"scope":"finite planted guard controls only; G/E universal claims OPEN"}
output.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps({"verdict":result["verdict"],"control_denominator":len(c.rows),"output":str(output)}))
try:
    from telemetry import gate,artifact,metric
    artifact(str(output));metric("guard controls completed",len(c.rows),total=len(c.rows),unit="checks")
    gate("known_truth","passed",detail="Frozen one-sided mutual-clear and original-edge controls; "+str(output))
except ImportError: pass
