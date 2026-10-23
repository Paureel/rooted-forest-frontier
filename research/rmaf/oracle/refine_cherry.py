#!/usr/bin/env python3
"""Post hoc candidate refinement over the discovery corpus, not certification."""
import json
from pathlib import Path
from oracle import TreeData, cherries, pair, validate, sha, write_json, ROOT, RESULTS, update_progress
from telemetry import step, metric, artifact

corpus = json.loads((RESULTS / "oracle-corpus.json").read_text())
spec = Path(__file__).with_name("local-rules-v2.json")
tested, kills = {}, {}
with step("compute", tool="rmaf-oracle"):
    for batch in corpus["batches"]:
        datas = [TreeData(pair(t,t)[0]) for t in batch["trees"]]
        for case in batch["cases"]:
            da, db = datas[case["a"]], datas[case["b"]]
            for cherry in cherries(da.tree):
                mask = db.embeddings[cherry]
                t = sum(bool(mask & db.bit[u]) and not bool(mask & db.bit[v]) for u,v in db.edges)
                if t < 2: continue
                tested[t] = tested.get(t,0) + 1
                if any([cherry[0]] in f or [cherry[1]] in f for f in case["forests"]): continue
                if t not in kills:
                    kills[t] = {"n":batch["n"], "a":da.tree, "b":db.tree, "cherry":cherry, "t":t, "k":case["k"], "all_optimal_forests":case["forests"], "witness":validate(da.tree,db.tree,case["forests"][0])}
        metric("completed", sum(tested.values()), unit="refined cherry cases")
receipt = {"convention":corpus["convention"], "rule_sha256":sha(spec), "corpus_sha256":sha(RESULTS/"oracle-corpus.json"), "tested_by_t":tested, "first_killer_by_t":kills, "status":"refuted-by-exact-enumeration" if kills else "finite-tests-only-not-proved", "independence":"Discovery corpus reused after v1 output; not an independent certificate.", "Lean":"not yet formalized"}
write_json(RESULTS / "oracle-local-rules-v2.json", receipt)
artifact("research/rmaf/results/oracle-local-rules-v2.json")
progress = json.loads((ROOT/"research/rmaf/progress/oracle.json").read_text())
progress["claims"].append({"id":"endpoint-only-t2", "label":"Drop side branch when t≥2", "status":"refuted" if kills else "open", "detail":f"{sum(tested.values())} exact small cases; {receipt['status']}. Post hoc discovery tests, not Lean."})
progress["artifacts"].append("research/rmaf/results/oracle-local-rules-v2.json")
write_json(ROOT/"research/rmaf/progress/oracle.json", progress)
print(json.dumps({"tested_by_t":tested,"status":receipt["status"],"killer_t":list(kills)}))
