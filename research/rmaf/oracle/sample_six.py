#!/usr/bin/env python3
"""Bounded exact n=6 discovery sample, with input draw frozen first."""
import json
from pathlib import Path
import random
import time
from oracle import all_trees, TreeData, partitions, optimum, cherries, validate, controls, sha, write_json, RESULTS, ROOT
from telemetry import step, metric, artifact

plan_path = Path(__file__).with_name("sample-plan-v1.json")
plan = json.loads(plan_path.read_text())
controls()
start = time.perf_counter()
trees = all_trees(tuple("abcdef"))
assert len(trees) == plan["expected_tree_count"]
assert len(partitions(tuple("abcdef"))) == plan["expected_partition_count"]
indices = sorted(random.Random(plan["seed"]).sample(range(len(trees)**2),plan["ordered_pair_sample"]))
write_json(RESULTS/"oracle-sample-six-inputs.json", {"plan_sha256":sha(plan_path),"indices":indices,"trees":trees})
datas = [TreeData(t) for t in trees]
setup_seconds = time.perf_counter()-start
cases, tested, kills = [], {}, {}
compute_start = time.perf_counter()
with step("compute",tool="rmaf-oracle"):
    for packed in indices:
        if time.perf_counter()-compute_start > plan["time_limit_seconds"]: break
        i,j = divmod(packed,len(trees))
        da,db = datas[i],datas[j]
        result = optimum(da.tree,db.tree,all_optima=True,data=(da,db))
        cases.append({"a":i,"b":j,"k":result["k"],"forests":result["forests"]})
        for cherry in cherries(da.tree):
            mask = db.embeddings[cherry]
            t = sum(bool(mask & db.bit[u]) and not bool(mask & db.bit[v]) for u,v in db.edges)
            if t<2: continue
            tested[t] = tested.get(t,0)+1
            if any((cherry[0],) in f or (cherry[1],) in f for f in result["forests"]): continue
            if t not in kills:
                kills[t] = {"a":da.tree,"b":db.tree,"cherry":cherry,"t":t,"k":result["k"],"all_optimal_forests":result["forests"],"witness":validate(da.tree,db.tree,[list(block) for block in result["forests"][0]])}
        if len(cases)%100==0: metric("completed",len(cases),total=len(indices),unit="six-leaf pairs")
elapsed=time.perf_counter()-compute_start
receipt={"n":6,"plan_sha256":sha(plan_path),"inputs_sha256":sha(RESULTS/"oracle-sample-six-inputs.json"),"requested_pairs":len(indices),"completed_pairs":len(cases),"setup_seconds":setup_seconds,"compute_seconds":elapsed,"tested_by_t":tested,"first_killer_by_t":kills,"cases":cases,"status":"refuted-by-exact-enumeration" if kills else "sample-tests-only-not-proved","Lean":"not yet formalized"}
write_json(RESULTS/"oracle-sample-six.json",receipt)
artifact("research/rmaf/results/oracle-sample-six.json")
p_path=ROOT/"research/rmaf/progress/oracle.json"
p=json.loads(p_path.read_text())
p["metrics"]["six_leaf_sample"]=len(cases)
p["claims"].append({"id":"endpoint-t2-six", "label":"Six-leaf cherry search", "status":"refuted" if kills else "open", "detail":f"{len(cases)} exact sampled pairs; {sum(tested.values())} eligible cherries. {receipt['status']}; not Lean."})
p["artifacts"].append("research/rmaf/results/oracle-sample-six.json")
write_json(p_path,p)
print(json.dumps({k:receipt[k] for k in ("completed_pairs","setup_seconds","compute_seconds","tested_by_t","status")}))
