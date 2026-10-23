"""One-shot bounded merged-origin/installed-library inventory, no proof replay."""
import hashlib,json,os,pathlib,subprocess,time
H=pathlib.Path(__file__).resolve().parent
ROOT=next(p for p in H.parents if(p/"bootloops-python").exists())
def main():
    names=json.loads((H/"source-dag.json").read_text())["order"]
    env=os.environ.copy();env["LEAN_PATH"]=str(H/"cold-source")
    argv=[str(ROOT/"bootloops-lean"),"--run",str(H/"MergedReadout.lean"),*names]
    start=time.perf_counter();p=subprocess.run(argv,cwd=H/"cold-source",env=env,text=True,capture_output=True,timeout=30)
    (H/"merged-readout.stdout").write_text(p.stdout);(H/"merged-readout.stderr").write_text(p.stderr)
    result={"argv":argv,"returncode":p.returncode,"seconds":time.perf_counter()-start,"source_sha256":hashlib.sha256((H/"MergedReadout.lean").read_bytes()).hexdigest()}
    (H/"merged-readout-execution.json").write_text(json.dumps(result,indent=2)+"\n")
    if p.returncode:raise RuntimeError("merged readout failed; logs preserved")
    r=json.loads(p.stdout);(H/"merged-readout.json").write_text(json.dumps(r,indent=2)+"\n")
    print(json.dumps({"scientific_producers":len(r["scientific_producers"]),"stored":sum(x["stored_count"]for x in r["scientific_producers"]),"resolved":len(r["resolved_scientific"]),"installed_modules":len(r["installed_modules"]),"seconds":result["seconds"]}))
if __name__=="__main__":main()
