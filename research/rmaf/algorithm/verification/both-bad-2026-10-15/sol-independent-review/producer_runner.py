#!/usr/bin/env python3
"""Fresh stored-producer control runner; reuses only this arm's toy subprocess helper."""
import copy
import json
import pathlib
import time
import toy_runner as own

HERE, TOYS = own.HERE, own.TOYS


def occurrence_map(rows):
    out = {}
    for r in rows:
        key = (r["producer"], r["index"], r["name"])
        if key in out: raise ValueError("duplicate-occurrence")
        out[key] = r
    return out


def errors(actual, claimed):
    failure = []
    for k in ["sources", "imports", "producer_inventories"]:
        if actual[k] != claimed[k]: failure.append(k)
    try:
        a = occurrence_map(actual["stored_occurrences"])
        b = occurrence_map(claimed["stored_occurrences"])
        if set(a) != set(b): failure.append("occurrence-bijection")
        for k in set(a)&set(b):
            if a[k] != b[k]: failure.append("stored-record")
    except ValueError:
        failure.append("duplicate-occurrence")
    if any(r["kind"] == "axiom" for r in claimed["stored_occurrences"]):
        failure.append("stored-direct-axiom")
    return failure


def main():
    start = time.perf_counter()
    summary = {"status":"RUNNING", "builds":[], "audits":{}, "plants":[]}
    for name in ["ProducerAudit","ToyProducer1","ToyProducer2","ToyProducerHostile"]:
        # Cold own-output rebuild, leaving other frozen toy products intact.
        for p in TOYS.glob(name + ".olean*"): p.unlink()
        summary["builds"].append(own.run(name))
        own.write(HERE / "producer-results-v2.json", summary)
    suites = {"Clean":["ToyProducer1","ToyProducer2"],
              "Hostile":["ToyProducer1","ToyProducerHostile"],
              "Reversed":["ToyProducerHostile","ToyProducer1"]}
    data = {}
    for label, modules in suites.items():
        name = "AuditProducer" + label
        oldout, newout = TOYS/(name+"-resolved.json"), TOYS/(name+"-stored.json")
        source = "import OriginAudit\nimport ProducerAudit\n" + "".join("import "+m+"\n" for m in modules)
        source += 'audit_origins! "'+str(oldout)+'"\naudit_producers! "'+str(newout)+'"\n'
        p = TOYS/(name+".lean"); p.write_text(source)
        summary["audits"][label] = {"source_sha256":own.sha(p)}
        own.write(HERE / "producer-results-v2.json",summary)
        summary["builds"].append(own.run(name))
        old = json.loads(oldout.read_text()); new = json.loads(newout.read_text())
        new["sources"] = {m+".lean":own.sha(TOYS/(m+".lean")) for m in modules}
        data[label] = new
        occurrence_map(new["stored_occurrences"])
        summary["audits"][label].update(
            stored_count=len(new["stored_occurrences"]), resolved_count=len(new["resolved_names"]),
            merged_rejected=old["rejected"], producer_rejected=new["rejected"],
            stored_output_sha256=own.sha(newout), resolved_output_sha256=own.sha(oldout))
        own.write(HERE / "producer-results-v2.json",summary)
    clean, hostile = data["Clean"], data["Hostile"]
    assert len(clean["stored_occurrences"]) == 4 and len(clean["resolved_names"]) == 3
    assert not clean["rejected"]
    assert len(hostile["stored_occurrences"]) == 4 and len(hostile["resolved_names"]) == 3
    assert not summary["audits"]["Hostile"]["merged_rejected"]
    hostile_rows = [r for r in hostile["stored_occurrences"] if r["producer"]=="ToyProducerHostile"]
    axiom = next(r for r in hostile_rows if r["kind"]=="axiom")
    assert axiom["name"]=="Shared.coalesced" and axiom["resolved_kind"]=="theorem"
    assert any(r["name"]=="ToyProducerHostile.own" for r in hostile["resolved_names"])
    assert any("stored-direct-axiom:ToyProducerHostile:Shared.coalesced"==r for r in hostile["rejected"])
    assert not errors(clean,copy.deepcopy(clean))
    def plant(name, change, detector):
        v=copy.deepcopy(clean); change(v)
        caught=errors(clean,v)
        assert detector in caught,(name,caught)
        summary["plants"].append({"name":name,"caught":caught})
    plant("missing-occurrence",lambda v:v["stored_occurrences"].pop(),"occurrence-bijection")
    plant("duplicate-occurrence",lambda v:v["stored_occurrences"].append(v["stored_occurrences"][0]),"duplicate-occurrence")
    plant("wrong-producer",lambda v:v["stored_occurrences"][0].update(producer="Wrong"),"occurrence-bijection")
    plant("wrong-kind",lambda v:v["stored_occurrences"][0].update(kind="opaque"),"stored-record")
    plant("wrong-type",lambda v:v["stored_occurrences"][0].update(type="wrong"),"stored-record")
    plant("wrong-body",lambda v:v["stored_occurrences"][0].update(body="wrong"),"stored-record")
    plant("wrong-source",lambda v:v["sources"].update({"ToyProducer1.lean":"f"*64}),"sources")
    plant("wrong-import",lambda v:v["imports"].append("Hidden"),"imports")
    plant("axiom-behind-clean-resolved",lambda v:v["stored_occurrences"][0].update(kind="axiom",resolved_kind="theorem"),"stored-direct-axiom")
    summary["status"]="PASS"
    summary["seconds"]=time.perf_counter()-start
    summary["scope"]="stored producer constants fully inventoried for Toy* modules; compiler extra names separately recorded, not claimed kernel bodies"
    own.write(HERE / "producer-results-v2.json",summary)
    print(json.dumps({"status":"PASS", "plants_caught":len(summary["plants"]),
                      "audits":summary["audits"], "seconds":summary["seconds"]}))


if __name__=="__main__":main()
