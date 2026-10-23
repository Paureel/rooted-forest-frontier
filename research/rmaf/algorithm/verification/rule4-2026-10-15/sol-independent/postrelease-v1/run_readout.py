"""One-shot capped actual Lean readout runner; all diagnostics retained."""
import argparse,hashlib,json,os,pathlib,subprocess,time
H=pathlib.Path(__file__).resolve().parent
ROOT=next(p for p in H.parents if(p/"bootloops-python").exists())
def main():
    p=argparse.ArgumentParser();p.add_argument("source");p.add_argument("tag");a=p.parse_args()
    src=H/a.source;env=os.environ.copy();env["LEAN_PATH"]=str(H/"cold-source")
    argv=[str(ROOT/"bootloops-lean"),"--run",str(src)];start=time.perf_counter()
    result=subprocess.run(argv,cwd=H/"cold-source",env=env,text=True,capture_output=True,timeout=30)
    receipt={"argv":argv,"returncode":result.returncode,"source_sha256":hashlib.sha256(src.read_bytes()).hexdigest(),"seconds":time.perf_counter()-start,"stdout":result.stdout,"stderr":result.stderr}
    (H/(a.tag+".json")).write_text(json.dumps(receipt,indent=2)+"\n")
    (H/(a.tag+".stdout")).write_text(result.stdout);(H/(a.tag+".stderr")).write_text(result.stderr)
    print(json.dumps({k:receipt[k]for k in["returncode","seconds","source_sha256"]}))
    if result.returncode:raise RuntimeError("readout failed; retained "+a.tag)
if __name__=="__main__":main()
