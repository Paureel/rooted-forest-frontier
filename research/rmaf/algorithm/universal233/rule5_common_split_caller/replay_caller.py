"""Exact-source graph subroutine replay; no full solver/runtime acceptance."""
from __future__ import annotations
import copy, gzip, hashlib, json, os, re, shutil, subprocess, time
from datetime import datetime, timezone
from pathlib import Path
from audit_caller import audit_source, parse_producer, ALLOWED

SRC=Path(__file__).resolve().parent
ROOT=SRC.parents[4]

def sha(p):
    h=hashlib.sha256()
    with open(p,"rb") as f:
        for b in iter(lambda:f.read(1048576),b""):h.update(b)
    return h.hexdigest()

def main():
    out=ROOT/"results"/("algorithm-universal233-common-split-caller-replay-"+datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ"))
    out.mkdir()
    env=dict(os.environ,LEAN_PATH=str(out))
    receipt={"status":"RUNNING_AUTHOR_GRAPH_REPLAY","all_three_main_milestones":"OPEN",
             "independent_acceptance":False,"full_algorithm":False,"runtime_claim":False,
             "runs":[],"source_inputs":[],"detector_controls":{},"archives":[]}
    def save(): (out/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    def run(name,build=False,timeout=60):
        start=time.monotonic()
        r=subprocess.run([str(ROOT/"bootloops-lean"),*(["-o",str(out/(name+".olean"))] if build else []),str(out/(name+".lean"))],cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=timeout)
        (out/(name+".log")).write_text(r.stdout)
        receipt["runs"].append({"module":name,"exit":r.returncode,"seconds":time.monotonic()-start,
                                "source_sha256":sha(out/(name+".lean")),"log_sha256":sha(out/(name+".log"))})
        save();return r
    def pin(p,h): assert sha(p)==h,("SOURCE_PIN_MISMATCH",str(p))
    pinfile=SRC/"CALLER-AUDIT-CONTROLS-v2.json"
    controls=json.loads(pinfile.read_text())
    for p,h in controls["pins"].items():pin(ROOT/p,h)
    shutil.copy2(SRC/"replay_caller.py",out/"replay_caller-executed.py")
    shutil.copy2(SRC/"audit_caller.py",out/"audit_caller-executed.py")
    shutil.copy2(pinfile,out/pinfile.name)
    receipt["detector_pin_sha256"]=sha(pinfile)
    receipt["timing_plan"]=controls["timing"]
    receipt["instrument_provenance"]="Exact completed frozen common-split graph audit helper/runner method reused as DEVELOPMENT; fresh caller-named Std-only instrument controls before first candidate application; mathematical consumer already authored/contacted; no reviewer implementation contact."
    def dump(name,imports,mods,bad=False):
        directory=out/(name+"-data");directory.mkdir()
        (out/(name+".lean")).write_text(audit_source(imports,mods,directory))
        r=run(name,False,240)
        assert (r.returncode!=0)==bad,(name,r.stdout)
        index=json.loads((directory/"index.json").read_text())
        assert {x["producer"] for x in index["producer_counts"]}==set(mods),"PRODUCER_SET"
        assert len(index["producer_counts"])==len(mods),"DUPLICATE_PRODUCER"
        rows=[];violations=[]
        for c in index["producer_counts"]:
            rr=json.loads((directory/c["file"]).read_text())
            violations.extend(parse_producer(c,rr,bad));rows.extend(rr)
        assert bool(violations)==bad and bool(index["rejects"])==bad,"WRONG_REJECT_RESULT"
        return directory,index,rows
    for name in ["CallerDetectorAlpha","CallerDetectorBeta","CallerDetectorHostile","CallerDetectorUnused"]:
        shutil.copy2(SRC/"detector_caller"/(name+".lean"),out/(name+".lean"))
        r=run(name,True);assert r.returncode==0,r.stdout
    coalesced=[]
    for name,mods,bad in [("DetectorClean",["CallerDetectorAlpha","CallerDetectorBeta"],False),
                          ("DetectorHostileAB",["CallerDetectorAlpha","CallerDetectorHostile"],True),
                          ("DetectorHostileBA",["CallerDetectorHostile","CallerDetectorAlpha"],True),
                          ("DetectorUnused",["CallerDetectorUnused"],True)]:
        _,idx,rows=dump(name,mods,mods,bad)
        receipt["detector_controls"][name]={"caught" if bad else "passed":True,"occurrences":len(rows)}
        shared=[r for r in rows if r["actual_name"]=="CallerDetectorShared.shared"]
        if not bad:
            assert len(shared)==2 and shared[0]["kind"]==shared[1]["kind"] and shared[0]["type"]==shared[1]["type"] and shared[0]["body"]==shared[1]["body"],"CLEAN_TWIN_BYTES"
            cleanidx,cleanrows=idx,rows
        else:
            coalesced.extend(r for r in shared if r["producer"]=="CallerDetectorHostile" and r["resolved_origin"]!="CallerDetectorHostile")
    assert coalesced,"COALESCED_HOSTILE_NOT_EXERCISED"
    receipt["detector_controls"]["coalesced_hostile_at_clean_origin"]=True
    c=cleanidx["producer_counts"][0]
    rr=[r for r in cleanrows if r["producer"]==c["producer"]]
    for label,mutate in [("missing",lambda r:r.pop()),("duplicate",lambda r:r.append(copy.deepcopy(r[0]))),
                         ("unresolved",lambda r:r[0].update(resolved_origin="<unresolved>"))]:
        corrupt=copy.deepcopy(rr);mutate(corrupt)
        try:parse_producer(c,corrupt)
        except AssertionError as e:receipt["detector_controls"][label]={"caught":True,"reason":str(e)}
        else:raise AssertionError("CORRUPTION_SURVIVED_"+label)
    save();print("Fresh producer detector controls passed before candidate audit.",flush=True)
    rows=json.loads((SRC/"CALLER-SOURCE-INPUTS-v1.json").read_text())
    for row in rows:
        p=ROOT/row["source"];pin(p,row["sha256"])
        text=p.read_text()
        stripped=re.sub(r"/\-.*?\-/",lambda m:"\n"*m.group().count("\n"),text,flags=re.S)
        stripped=re.sub(r"--[^\n]*","",stripped)
        assert not re.search(r"\b(sorry|admit|axiom|native_decide)\b",stripped),("PROOF_ESCAPE",row["module"])
        shutil.copy2(p,out/(row["module"]+".lean"))
        receipt["source_inputs"].append({**row,"copied_sha256":sha(out/(row["module"]+".lean")),"adaptations":"none; exact bytes"})
    for i,row in enumerate(rows):
        r=run(row["module"],True)
        assert r.returncode==0 and "sorryAx" not in r.stdout and "declaration uses" not in r.stdout,(row["module"],r.stdout)
        if (i+1)%20==0:print("Built",i+1,"/",len(rows),"exact scientific modules.",flush=True)
    for name,count in [("FalseControls",5),("GraphFalse",4),("CallerFalse",2),("PaidFalse",2),("OutsideFalse",2),("GuardedFalse",2),("RefusalFalse",1)]:
        shutil.copy2(SRC/(name+".lean"),out/(name+".lean"));r=run(name)
        assert r.returncode!=0 and r.stdout.count("is false")==count,(name,r.stdout)
    for name in ["CallerAxioms"]:
        shutil.copy2(SRC/(name+".lean"),out/(name+".lean"));r=run(name);assert r.returncode==0 and "sorryAx" not in r.stdout,r.stdout
    mods=[r["module"] for r in rows]
    directory=out/"producer-records";directory.mkdir()
    (out/"CallerOccurrenceAudit.lean").write_text(audit_source(["CallerFinal"],mods,directory))
    r=run("CallerOccurrenceAudit",False,240);assert r.returncode==0,r.stdout
    index=json.loads((directory/"index.json").read_text())
    assert len(index["producer_counts"])==len(mods) and {x["producer"] for x in index["producer_counts"]}==set(mods)
    assert not index["rejects"]
    compact=[];names=set();axioms=set()
    for c in index["producer_counts"]:
        p=directory/c["file"];raw=json.loads(p.read_text());parse_producer(c,raw)
        for row in raw:
            names.add(row["actual_name"]);axioms.update(row["axiom_references"])
            compact.append({**{k:v for k,v in row.items() if k not in ["type","body"]},
                            "type_sha256":hashlib.sha256(row["type"].encode()).hexdigest(),
                            "body_sha256":hashlib.sha256(row["body"].encode()).hexdigest()})
        rawhash=sha(p);rawbytes=p.stat().st_size;archive=p.with_suffix(".json.gz")
        with open(p,"rb") as f,gzip.open(archive,"wb",compresslevel=6) as z:shutil.copyfileobj(f,z,1048576)
        h=hashlib.sha256();size=0
        with gzip.open(archive,"rb") as z:
            for b in iter(lambda:z.read(1048576),b""):h.update(b);size+=len(b)
        assert h.hexdigest()==rawhash and size==rawbytes,"LOSSLESS_ROUNDTRIP"
        receipt["archives"].append({"producer":c["producer"],"file":str(archive.relative_to(out)),"bytes":archive.stat().st_size,
            "sha256":sha(archive),"raw_bytes":rawbytes,"raw_sha256":rawhash,"roundtrip_match":True})
        p.unlink()
    assert axioms<=ALLOWED
    (out/"producer-inventory.json").write_text(json.dumps(compact,indent=2)+"\n")
    for row in receipt["source_inputs"]:
        pin(ROOT/row["source"],row["sha256"]);pin(out/(row["module"]+".lean"),row["copied_sha256"])
    plant=out/"SourcePinPlant.lean";sample=out/"GuardedExact.lean"
    plant.write_bytes(sample.read_bytes()+b"\n-- deliberate byte corruption\n")
    try:pin(plant,sha(sample))
    except AssertionError as e:receipt["detector_controls"]["source_byte_plant"]={"caught":True,"reason":str(e)}
    else:raise AssertionError("SOURCE_PIN_PLANT_SURVIVED")
    receipt.update(status="PASS_AUTHOR_COMMON_SPLIT_CALLER_SOURCE_BOUND",scientific_modules=len(mods),
        stored_producer_occurrences=len(compact),resolved_unique_scientific_names=len(names),axiom_union=sorted(axioms),
        original_graph_positive_groups=9,postconstruction_graph_positive_groups=7,caller_stage_positive_groups=16,postconstruction_refusal_groups=2,false_propositions_rejected=18,
        exact_source_adaptations=0,source_runtime_claim=False,
        theorem="runGuarded_answer_exact: SAME executable literal reconstruction/outside depth01+cost2 witness/actual guarded q-1 callback LIST bounded exact under actual-child IH; explicit refusal boundary",
        first_open_algorithm_call="Admitted source Rule5.3.1 must construct actual Setup and prove outside minimum1/nonrefusal; local source-cost correspondence/full dispatcher and mutual runtime remain OPEN")
    for p,h in controls["pins"].items():pin(ROOT/p,h)
    receipt["runner_self_pin_before_and_after"]=True
    save();print(receipt["status"],len(mods),"modules",len(compact),"producer occurrences",flush=True)
    print(out,flush=True)

if __name__=="__main__":main()
