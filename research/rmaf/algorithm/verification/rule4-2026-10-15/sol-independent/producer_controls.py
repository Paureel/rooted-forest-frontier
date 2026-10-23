"""One-shot prerelease Std-only producer audit controls; no scientific imports.
The same record validator is intended for isolated postrelease producer audits.
"""
import argparse,copy,hashlib,json,os,pathlib,subprocess,time,traceback
H=pathlib.Path(__file__).resolve().parent; C=H/"producer-controls"
# Resolve by workspace ancestor, never scientific candidate paths.
ROOT=next(p for p in H.parents if (p/"bootloops-python").exists())
LEAN=ROOT/".runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"
LOG=H/"producer-execution-v1.jsonl"

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def run(argv,tag,expected=0):
    original_tag=tag; attempt=1
    while (H/(tag+".stdout")).exists():
        attempt+=1;tag=original_tag+"-attempt"+str(attempt)
    t=time.perf_counter(); env=os.environ.copy(); env["LEAN_PATH"]=str(C)
    try:
        p=subprocess.run([str(x) for x in argv],cwd=C,env=env,text=True,capture_output=True,timeout=30)
        result={"tag":tag,"argv":[str(x) for x in argv],"returncode":p.returncode,"elapsed_seconds":time.perf_counter()-t,"stdout":p.stdout,"stderr":p.stderr}
    except Exception as e:
        result={"tag":tag,"argv":[str(x) for x in argv],"exception":repr(e),"elapsed_seconds":time.perf_counter()-t}
        with LOG.open("a")as f:f.write(json.dumps(result)+"\n")
        raise
    with LOG.open("a")as f:f.write(json.dumps(result)+"\n")
    (H/(tag+".stdout")).write_text(p.stdout); (H/(tag+".stderr")).write_text(p.stderr)
    if p.returncode!=expected: raise AssertionError((tag,p.returncode,expected,p.stdout,p.stderr))
    return result

def pin_sources():
    paths=sorted(C.glob("*.lean"))+[H/"ProducerAudit.lean",H/"producer_controls.py"]
    return {str(p):digest(p) for p in paths}

def validate(record,pins):
    for name,sha in pins.items():
        if digest(pathlib.Path(name))!=sha: raise ValueError("SOURCE_PIN_MISMATCH")
    rows=record["occurrences"]; inv=record["inventories"]
    if len(rows)!=record["occurrence_count"]: raise ValueError("OCCURRENCE_COUNT_MISMATCH")
    names=[x["producer"] for x in inv]
    if len(names)!=len(set(names)) or set(names)!=set(record["producers"]):raise ValueError("PRODUCER_MISMATCH")
    for info in inv:
        selected=[r for r in rows if r["producer"]==info["producer"]]
        if len(selected)!=info["count"] or len(info["names"])!=info["count"]:raise ValueError("MISSING_OR_DUPLICATE_OCCURRENCE")
        if [r["index"] for r in selected]!=list(range(info["count"])):raise ValueError("BAD_OCCURRENCE_INDEX")
        if [r["name"] for r in selected]!=info["names"]:raise ValueError("BAD_OCCURRENCE_NAME")
        if any(r["imports"]!=info["imports"] for r in selected):raise ValueError("IMPORT_MISMATCH")
    if record["forbidden"] or record["unresolved"] or not record["ok"]:raise ValueError("CUSTOM_AXIOM_OR_UNRESOLVED")
    if any(r["kind"]=="axiom" and r["name"]not in ["propext","Classical.choice","Quot.sound"] for r in rows): raise ValueError("DIRECT_CUSTOM_AXIOM")
    return True

def frozen_equal(record,reference):
    # Exact byte/type/body/import adaptation comparator; names cannot mask bodies.
    if record!=reference:raise ValueError("STORED_RECORD_ADAPTATION")

def catches(fn):
    try:fn()
    except (AssertionError,ValueError,KeyError):return True
    return False

def audit(modules,tag,expected=0):
    result=run([LEAN,"--run",H/"ProducerAudit.lean",*modules],tag,expected)
    record=json.loads(result["stdout"])
    (H/(tag+".json")).write_text(json.dumps(record,indent=2)+"\n")
    return record

def main():
    p=argparse.ArgumentParser();p.add_argument("--mode",choices=["pilot","battery"],required=True);a=p.parse_args()
    pins=pin_sources(); (H/("producer-source-pins-"+a.mode+"-v1.json")).write_text(json.dumps(pins,indent=2)+"\n")
    results=[]
    def check(name,value):
        results.append({"name":name,"passed":bool(value)})
        if not value:raise AssertionError(name)
    if a.mode=="pilot":
        compile=run([LEAN,"-o",C/"SolCleanA.olean",C/"SolCleanA.lean"],"pilot-clean-compile")
        clean=audit(["SolCleanA"],"pilot-clean-audit")
        check("Std clean stored occurrence",validate(clean,pins) and clean["occurrence_count"]==1 and clean["occurrences"][0]["name"]=="SolSame.token")
    else:
        for name in ["SolCleanA","SolCleanB","SolHostile","SolUnused","SolPrivate"]:
            run([LEAN,"-o",C/(name+".olean"),C/(name+".lean")],"battery-compile-"+name)
        false=run([LEAN,"-o",C/"SolFalse.olean",C/"SolFalse.lean"],"battery-false-compile",1)
        check("Std false rejected",false["returncode"]!=0)
        clean=audit(["SolCleanA","SolCleanB"],"battery-clean-AB")
        cleanBA=audit(["SolCleanB","SolCleanA"],"battery-clean-BA")
        check("clean twins AB",validate(clean,pins) and clean["occurrence_count"]==2)
        check("clean twins BA",validate(cleanBA,pins) and cleanBA["occurrence_count"]==2)
        check("same name actual occurrences",[r["name"]for r in clean["occurrences"]]==["SolSame.token","SolSame.token"])
        for modules,tag in [(["SolHostile"],"hostile"),(["SolCleanA","SolHostile"],"coalesced-AH"),(["SolHostile","SolCleanA"],"coalesced-HA"),(["SolUnused"],"unused"),(["SolPrivate"],"private-generated")]:
            bad=audit(modules,"battery-"+tag,2)
            check("reject "+tag,catches(lambda:validate(bad,pins)))
            if "coalesced"in tag:
                check("hostile actual axiom retained "+tag,any(r["producer"]=="SolHostile"and r["name"]=="SolSame.token"and r["kind"]=="axiom"for r in bad["occurrences"]))
                check("hostile own clean retained "+tag,any(r["name"]=="SolSame.hostileOwnClean"for r in bad["occurrences"]))
            if tag=="private-generated":
                check("private axiom retained",any(r["kind"]=="axiom"and"hidden"in r["name"]for r in bad["occurrences"]))
                check("generated dependency retained",any("generated"in r["name"]and any("hidden"in ax for ax in r["axioms"])for r in bad["occurrences"]))
        for tag,mutate in [
            ("missing row",lambda r:r["occurrences"].pop()),
            ("duplicate row",lambda r:r["occurrences"].append(copy.deepcopy(r["occurrences"][0]))),
            ("missing inventory",lambda r:r["inventories"][0]["names"].pop()),
            ("duplicate inventory",lambda r:r["inventories"][0]["names"].append("SolSame.token")),
            ("index",lambda r:r["occurrences"][0].update(index=99)),
            ("import",lambda r:r["occurrences"][0].update(imports=["BadImport"])),
            ("type",lambda r:r["occurrences"][0].update(type="changed type bytes")),
            ("body",lambda r:r["occurrences"][0].update(body="changed body bytes"))]:
            bad=copy.deepcopy(clean);mutate(bad)
            check("reject corruption "+tag,catches(lambda:validate(bad,pins))or catches(lambda:frozen_equal(bad,clean)))
            check("clean twin "+tag,validate(clean,pins) and frozen_equal(clean,clean)is None)
        wrongpins=copy.deepcopy(pins);wrongpins[str(C/"SolCleanA.lean")]="0"*64
        check("source bytes reject",catches(lambda:validate(clean,wrongpins)))
        # Pin installed library artifacts rather than rebuilding Std.
        lib=LEAN.parent.parent/"lib/lean"
        stdpaths=[lib/"Std.olean",lib/"Init.olean",lib/"Lean.olean",LEAN]
        (H/"installed-library-pins-v1.json").write_text(json.dumps({str(p):digest(p)for p in stdpaths},indent=2)+"\n")
    (H/("producer-"+a.mode+"-results-v1.json")).write_text(json.dumps({"checks":results,"passed":len(results),"source_pins":pins},indent=2)+"\n")
    print(json.dumps({"mode":a.mode,"passed":len(results)}))
if __name__=="__main__":
    try:main()
    except Exception:
        with (H/"producer-failures-v1.log").open("a")as f:f.write(traceback.format_exc()+"\n")
        raise
