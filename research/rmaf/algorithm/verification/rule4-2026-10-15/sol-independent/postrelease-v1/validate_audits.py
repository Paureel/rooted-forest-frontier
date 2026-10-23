"""One-shot exact stored-byte audit validation; fresh scientific source only.
Uses unchanged precontact record validator; processes one gzip producer at a time.
"""
import argparse,gzip,hashlib,json,pathlib,sys,time
H=pathlib.Path(__file__).resolve().parent;PRE=H.parent
sys.path.insert(0,str(PRE));import producer_controls as pc
def file_sha(p):
    d=hashlib.sha256()
    with p.open("rb")as f:
        while b:=f.read(1024*1024):d.update(b)
    return d.hexdigest()
def main():
    p=argparse.ArgumentParser();p.add_argument("--limit",type=int,required=True);p.add_argument("--output",required=True);a=p.parse_args();start=time.perf_counter()
    dag=json.loads((H/"source-dag.json").read_text());merged=json.loads((H/"merged-readout.json").read_text())
    inventory={x["producer"]:x for x in merged["scientific_producers"]}
    if set(inventory)!=set(dag["order"]):raise ValueError("PRODUCER_CLOSURE_MISMATCH")
    pins={str(H/"cold-source"/(name+".lean")):r["sha256"]for name,r in dag["sources"].items()}
    readyManifest=json.loads((PRE/"PRERELEASE-MANIFEST-v1.json").read_text())
    auditorPin=next(r["sha256"]for r in readyManifest["files"]if r["path"]=="ProducerAudit.lean")
    pins[str(PRE/"ProducerAudit.lean")]=auditorPin
    summaries=[];allnames=set();axioms=set();occurrences=0;extras=0;unknown=[]
    for name in dag["order"][:a.limit]:
        t=time.perf_counter();path=H/"producer-audits"/(name+".json.gz");meta=json.loads(path.with_name(name+".meta.json").read_text())
        if meta["returncode"]or meta["timeout"]or meta["auditor_sha256"]!=auditorPin:raise ValueError("AUDIT_EXECUTION_MISMATCH")
        if file_sha(path)!=meta["gzip_sha256"]:raise ValueError("GZIP_PIN_MISMATCH")
        with gzip.open(path,"rb")as f:raw=f.read(400000001)
        if len(raw)!=meta["uncompressed_bytes"]or hashlib.sha256(raw).hexdigest()!=meta["uncompressed_sha256"]:raise ValueError("UNCOMPRESSED_PIN_MISMATCH")
        r=json.loads(raw);del raw
        pc.validate(r,pins)
        if r["producers"]!=[name]or r["occurrence_count"]!=inventory[name]["stored_count"]:raise ValueError("STORED_INVENTORY_COUNT_MISMATCH")
        names=[row["name"]for row in r["occurrences"]]
        if names!=inventory[name]["stored_names"]:raise ValueError("STORED_ARRAY_INDEX_NAME_MISMATCH")
        # Automatic Init imports are installed Lean loader metadata; retain exactly.
        actualImports=r["inventories"][0]["imports"]
        if [i for i in actualImports if i!="Init"]!=dag["sources"][name]["imports"]:raise ValueError("EXPLICIT_IMPORT_ADAPTATION")
        if actualImports!=inventory[name]["imports"]:raise ValueError("MERGED_IMPORT_MISMATCH")
        for row in r["occurrences"]:
            if row["kind"]=="axiom":raise ValueError("DIRECT_SCIENTIFIC_AXIOM")
            if not row["type"]or row["kind"]in["theorem","definition","opaque"]and row["body"]is None:raise ValueError("MISSING_ACTUAL_TYPE_BODY")
            axioms.update(row["axioms"]);allnames.add(row["name"])
        for x in inventory[name]["extra_names"]:
            if x["has_constant_info"]:
                extras+=1
                if x["name"]not in names:unknown.append({"producer":name,"extra":x["name"]})
        occurrences+=r["occurrence_count"]
        summaries.append({"producer":name,"occurrences":r["occurrence_count"],"imports":actualImports,"uncompressed_bytes":meta["uncompressed_bytes"],"seconds":time.perf_counter()-t})
        if time.perf_counter()-t>30:raise TimeoutError("producer parse30s cap")
        del r
    if unknown:raise ValueError(("UNINSPECTED_EXTRA_CONSTANTINFO",unknown))
    full=a.limit>=len(dag["order"])
    if full:
        resolved=merged["resolved_scientific"]
        if len(allnames)!=len(resolved)or allnames!={x["name"]for x in resolved}:raise ValueError("RESOLVED_NAME_CLOSURE_MISMATCH")
        if any(x["producer"]not in inventory for x in resolved):raise ValueError("UNATTRIBUTABLE_SCIENTIFIC_RESOLUTION")
    result={"complete":full,"producers":len(summaries),"stored_occurrences":occurrences,"unique_names":len(allnames),"axiom_union":sorted(axioms),"actual_extra_ConstantInfos_already_in_arrays":extras,"uninspected_extra_ConstantInfos":unknown,"summaries":summaries,"seconds":time.perf_counter()-start,"copied_scientific_oleans":0,"qualification":"stored occurrence arrays inspected before considering resolved origin; full actual type/body/reference bytes retained in gzip; counts inventory only"}
    (H/a.output).write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:result[k]for k in["complete","producers","stored_occurrences","unique_names","axiom_union","actual_extra_ConstantInfos_already_in_arrays","seconds"]}))
if __name__=="__main__":main()
