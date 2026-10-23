"""One-shot pin of actually imported installed Std/Init artifact closure.
No standard library rebuild or scientific candidate cache is substituted.
"""
import hashlib,json,pathlib,time
H=pathlib.Path(__file__).resolve().parent
ROOT=next(p for p in H.parents if(p/"bootloops-python").exists())
def sha(p):
    d=hashlib.sha256();t=time.perf_counter()
    with p.open("rb")as f:
        while b:=f.read(1024*1024):
            d.update(b)
            if time.perf_counter()-t>30:raise TimeoutError("installed artifact30s cap")
    return d.hexdigest()
def main():
    start=time.perf_counter();m=json.loads((H/"merged-readout.json").read_text());paths=set()
    base=ROOT/".runtime/elan/toolchains/leanprover--lean4---v4.35.0"
    for mod in m["installed_modules"]:
        if mod["module"].split(".")[0]not in("Init","Std"):raise ValueError("unqualified installed module")
        p=pathlib.Path(mod["olean"])
        if not p.is_relative_to(base):raise ValueError("unqualified installed artifact path")
        for suffix in[".olean",".olean.server",".olean.private",".ir",".ir.server",".ir.private"]:
            candidate=p.with_suffix(suffix)
            if candidate.exists():paths.add(candidate)
    paths.add(base/"bin/lean")
    paths.update((base/"lib/lean").glob("*.dylib"))
    paths=sorted(paths)
    pilot=[]
    for p in paths[:8]:
        t=time.perf_counter();pilot.append({"path":str(p),"sha256":sha(p),"bytes":p.stat().st_size,"seconds":time.perf_counter()-t})
    (H/"installed-pin-pilot.json").write_text(json.dumps(pilot,indent=2)+"\n")
    rows=[]
    for p in paths:
        rows.append({"path":str(p),"bytes":p.stat().st_size,"sha256":sha(p)})
    out={"imported_standard_modules":len(m["installed_modules"]),"artifacts":rows,"count":len(rows),"bytes":sum(r["bytes"]for r in rows),"seconds":time.perf_counter()-start,"qualification":"installed Std/Init/toolchain pins, not source rebuild; compiled instruction equivalence not claimed"}
    (H/"installed-used-pins.json").write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps({k:out[k]for k in["imported_standard_modules","count","bytes","seconds"]}))
if __name__=="__main__":main()
