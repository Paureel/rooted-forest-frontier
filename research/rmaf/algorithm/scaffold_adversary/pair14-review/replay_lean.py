"""Replay released Lean sources in owned copies; never run mutating author audit."""
from pathlib import Path
import os,subprocess,time,json,re,hashlib
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
D=HERE/"lean-replay"
env=os.environ.copy()
env["LEAN_PATH"]=str(D)
runs=[]


def run(name,build=False,timeout=45):
    cmd=[str(ROOT/"bootloops-lean")]
    if build:
        cmd += ["-o",name+".olean"]
    cmd += [name+".lean"]
    start=time.perf_counter()
    p=subprocess.run(cmd,cwd=D,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=timeout)
    (HERE/(name+"-own-replay.log")).write_text(p.stdout)
    rec={"name":name,"command":cmd,"returncode":p.returncode,"seconds":time.perf_counter()-start,"source_sha256":hashlib.sha256((D/(name+".lean")).read_bytes()).hexdigest()}
    runs.append(rec)
    (HERE/"lean-replay-progress.json").write_text(json.dumps(runs,indent=2)+"\n")
    print(json.dumps(rec),flush=True)
    return p


def main():
    version=subprocess.run([str(ROOT/"bootloops-lean"),"--version"],cwd=D,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=20)
    (HERE/"lean-version.log").write_text(version.stdout)
    if version.returncode!=0 or "4.35.0" not in version.stdout:
        raise AssertionError("released Lean4.35 toolchain unavailable")
    for name in ["RMAF","CoreGraph","CoreProgram","PairWitness"]:
        p=run(name,True)
        if p.returncode:
            raise AssertionError(("source replay failed",name,p.stdout))
    p=run("AxiomInventory")
    if p.returncode:
        raise AssertionError("complete author-module axiom inventory failed")
    modules=re.findall(r"^MODULE\|([^|]+)\|(.+)$",p.stdout,re.M)
    audits=re.findall(r"^MODAUDIT\|([^|]+)\|\[(.*?)\]$",p.stdout,re.M)
    if len(modules)!=len(audits) or {n for _,n in modules}!={n for n,_ in audits}:
        raise AssertionError("incomplete declaration axiom closure")
    axiom_union=sorted({a.strip() for _,axes in audits for a in axes.split(",") if a.strip()})
    if not set(axiom_union)<={"propext","Quot.sound","Classical.choice"}:
        raise AssertionError("unapproved production axiom")
    false=run("FalsePairWitness")
    if false.returncode==0 or false.stdout.count("proved that the proposition")!=2 or false.stdout.count("is false")!=2:
        raise AssertionError("author false controls did not fail for intended false propositions")
    clean=run("LeanCleanControl",True)
    if clean.returncode or clean.stdout.count("does not depend on any axioms")!=2:
        raise AssertionError("prepared clean axiom-free controls failed")
    negative=run("LeanFalseControl")
    if negative.returncode==0 or "is false" not in negative.stdout:
        raise AssertionError("prepared false proposition not caught")
    plant=run("LeanAxiomPlant",True)
    if plant.returncode or "pair14_planted_false" not in plant.stdout:
        raise AssertionError("custom-axiom plant did not compile and expose closure")
    detector=run("ControlAxiomAudit")
    if detector.returncode==0 or "REJECT_CUSTOM_AXIOM|pair14_contaminated_false_control|pair14_planted_false" not in detector.stdout:
        raise AssertionError("compilable false axiom plant escaped audit")
    prod=run("ProductionReadout")
    if prod.returncode:
        raise AssertionError("production generator readout failed")
    outputs={name:json.loads(body) for name,body in re.findall(r"^PRODJSON\|([^|]+)\|(.+)$",prod.stdout,re.M)}
    if set(outputs)!={"A","ASwap","B","BSwap","AUnderBudget"}:
        raise AssertionError("missing production readout")
    (HERE/"production-readout.json").write_text(json.dumps(outputs,indent=2)+"\n")
    scan=[]
    for name in ["RMAF","CoreGraph","CoreProgram","PairWitness"]:
        text=(D/(name+".lean")).read_text()
        hits=re.findall(r"\b(sorry|admit|native_decide)\b",text)
        declarations=re.findall(r"^\s*axiom\s+([^\s:]+)",text,re.M)
        scan.append({"module":name,"forbidden_tokens":hits,"explicit_axiom_declarations":declarations})
        if hits or declarations:
            raise AssertionError("forbidden production proof source declaration/token")
    result={"toolchain":version.stdout.strip(),"runs":runs,"audited_declarations":len(modules),"module_counts":{m:sum(mod==m for mod,_ in modules) for m in sorted({mod for mod,_ in modules})},"axiom_union":axiom_union,"source_scan":scan,"author_false_propositions_caught":2,"prepared_false_propositions_caught":1,"compilable_custom_axiom_plant_rejected":True,"production_readout":outputs,"scope":"source-bound finite Lean replay and complete originating-module axiom closures; not complete Figure16, exhaustive-selector or universal runtime formalization"}
    (HERE/"lean-own-audit.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"complete":True,"declarations":len(modules),"axioms":axiom_union,"false_propositions":3,"custom_axiom_plant_rejected":True}),flush=True)


if __name__=="__main__":
    main()
