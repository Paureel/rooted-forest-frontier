"""One-shot independent exact-source staging/build driver, release scope only.
No author checker/implementation is imported. Scientific source copies retain bytes;
scientific oleans are generated here from zero, and LEAN_PATH is only this replay.
"""
import argparse,hashlib,json,os,pathlib,re,shutil,subprocess,time,traceback
H=pathlib.Path(__file__).resolve().parent; PRE=H.parent
ROOT=next(p for p in H.parents if(p/"bootloops-python").exists())
MAN=ROOT/"research/rmaf/algorithm/universal233/rule4/RULE4-MANIFEST-v1.json"
REPLAY=H/"cold-source"; LOG=H/"build-execution.jsonl"
def dump(name,obj): (H/name).write_text(json.dumps(obj,indent=2)+"\n")
def digest(p):
    start=time.perf_counter(); d=hashlib.sha256()
    with p.open("rb")as f:
        while chunk:=f.read(1024*1024):
            d.update(chunk)
            if time.perf_counter()-start>30:raise TimeoutError("file hash30s cap")
    return d.hexdigest()
def prepare():
    start=time.perf_counter(); release=ROOT/"research/rmaf/algorithm/verification/rule4-2026-10-15/ROOT-RELEASE-v1.json"
    rel=json.loads(release.read_text());assert rel["status"]=="EXACT_COMPLETED_SOURCE_RELEASED_FOR_REVIEW_NOT_ACCEPTED"
    assert digest(PRE/"READY-v1.json")==rel["READY_sha256"]
    assert digest(MAN)==rel["author_manifest_sha256"]
    m=json.loads(MAN.read_text());entries=m["immutable_files"]+m["external_input_pins"]
    # First small measured bounded slice: eight listed files, then1MiB of largest.
    pilot=[]
    for row in entries[:8]:
        t=time.perf_counter();assert digest(ROOT/row["path"])==row["sha256"]
        pilot.append({"path":row["path"],"bytes":row["bytes"],"seconds":time.perf_counter()-t})
    largest=max(entries,key=lambda x:x["bytes"]);t=time.perf_counter()
    with(ROOT/largest["path"]).open("rb")as f: chunk=f.read(1024*1024)
    hashlib.sha256(chunk).hexdigest();pilot.append({"prefix_only":largest["path"],"bytes":len(chunk),"seconds":time.perf_counter()-t})
    dump("hash-pilot.json",pilot)
    receipts=[]
    for row in entries:
        t=time.perf_counter();p=ROOT/row["path"]
        actual=digest(p); ok=actual==row["sha256"]and p.stat().st_size==row["bytes"]
        receipts.append({"path":row["path"],"sha256":actual,"bytes":p.stat().st_size,"match":ok,"seconds":time.perf_counter()-t})
        if not ok:dump("pin-failure.json",receipts);raise ValueError("SOURCE_PIN_MISMATCH")
    dump("pins-rechecked.json",{"records":receipts,"count":len(receipts),"elapsed_seconds":time.perf_counter()-start,"root_release_sha256":digest(release)})
    # Use only canonical exact scientific source snapshots, not its oleans/logs/auditor.
    canon=pathlib.Path(m["canonical_receipt"]).parent
    catalog={pathlib.Path(r["path"]).stem:r for r in entries if pathlib.Path(r["path"]).parent==canon and r["path"].endswith(".lean")}
    order=[];state={};sources={}
    def visit(name):
        if name in("Std","Lean","Init")or name.startswith(("Std.","Lean.","Init.")):return
        if state.get(name)==2:return
        if state.get(name)==1:raise ValueError("import cycle "+name)
        if name not in catalog:raise ValueError("UNPINNED_IMPORT "+name)
        state[name]=1; row=catalog[name];p=ROOT/row["path"];text=p.read_text()
        imports=[]
        for line in text.splitlines():
            if match:=re.match(r"^\s*(?:public\s+|private\s+)?import\s+(.+?)\s*$",line):
                imports.extend(match.group(1).split("--")[0].split())
        sources[name]={**row,"imports":imports}
        for dep in imports:visit(dep)
        state[name]=2;order.append(name)
    for root in("Rule4Solve","Rule4Controls","Rule4Costs"):visit(root)
    REPLAY.mkdir(exist_ok=False)
    for name in order:
        row=sources[name];shutil.copyfile(ROOT/row["path"],REPLAY/(name+".lean"))
        assert digest(REPLAY/(name+".lean"))==row["sha256"]
    shutil.copyfile(ROOT/"research/rmaf/lean/lean-toolchain",REPLAY/"lean-toolchain")
    dump("source-dag.json",{"order":order,"count":len(order),"sources":sources,"copied_scientific_oleans":0,"LEAN_PATH":str(REPLAY)})
    print(json.dumps({"pins":len(receipts),"sources":len(order),"prepare_seconds":time.perf_counter()-start,"first_modules":order[:5]}))
def build(limit):
    dag=json.loads((H/"source-dag.json").read_text());done=set()
    if LOG.exists():
        for line in LOG.read_text().splitlines():
            r=json.loads(line)
            if r.get("returncode")==0:done.add(r["module"])
    pending=[m for m in dag["order"]if m not in done][:limit]
    if not pending:raise ValueError("no pending sources in requested slice")
    env=os.environ.copy();env["LEAN_PATH"]=str(REPLAY)
    for name in pending:
        source=REPLAY/(name+".lean");expected=dag["sources"][name]["sha256"]
        if digest(source)!=expected:raise ValueError("SOURCE_PIN_MISMATCH "+name)
        t=time.perf_counter();argv=[str(ROOT/"bootloops-lean"),"-o",str(REPLAY/(name+".olean")),str(source)]
        p=subprocess.run(argv,cwd=REPLAY,env=env,capture_output=True,text=True,timeout=30)
        out={"module":name,"argv":argv,"returncode":p.returncode,"seconds":time.perf_counter()-t,"source_sha256":expected,"stdout":p.stdout,"stderr":p.stderr,"LEAN_PATH":env["LEAN_PATH"]}
        with LOG.open("a")as f:f.write(json.dumps(out)+"\n")
        (H/("build-"+name+".log")).write_text(p.stdout+p.stderr)
        if p.returncode:raise ValueError("BUILD_FAILED "+name)
    print(json.dumps({"slice_compiled":len(pending),"total_compiled":len(done)+len(pending),"remaining":len(dag["order"])-len(done)-len(pending)}))
def main():
    p=argparse.ArgumentParser();p.add_argument("--prepare",action="store_true");p.add_argument("--build",type=int);a=p.parse_args()
    if a.prepare:prepare()
    elif a.build:build(a.build)
    else:raise ValueError("explicit bounded stage required")
if __name__=="__main__":
    try:main()
    except Exception:
        with(H/"driver-failures.log").open("a")as f:f.write(traceback.format_exc()+"\n")
        raise
