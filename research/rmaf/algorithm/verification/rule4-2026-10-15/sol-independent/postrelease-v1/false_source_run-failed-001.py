"""One-shot exact released negative-source compilation; no source adaptation."""
import hashlib,json,os,pathlib,shutil,subprocess,time
H=pathlib.Path(__file__).resolve().parent
ROOT=next(p for p in H.parents if(p/"bootloops-python").exists())
def main():
    rel="research/rmaf/algorithm/universal233/rule4/Rule4False.lean"
    m=json.loads((ROOT/"research/rmaf/algorithm/universal233/rule4/RULE4-MANIFEST-v1.json").read_text())
    expected=next(x["sha256"]for x in m["immutable_files"]if x["path"]==rel)
    src=ROOT/rel;assert hashlib.sha256(src.read_bytes()).hexdigest()==expected
    dest=H/"false-source";dest.mkdir(exist_ok=True);copy=dest/"Rule4False.lean";shutil.copyfile(src,copy)
    env=os.environ.copy();env["LEAN_PATH"]=str(H/"cold-source");start=time.perf_counter()
    argv=[str(ROOT/"bootloops-lean"),"-o",str(dest/"Rule4False.olean"),str(copy)]
    p=subprocess.run(argv,cwd=H/"cold-source",env=env,text=True,capture_output=True,timeout=30)
    errors=[line for line in p.stdout.splitlines()if"error"in line]
    out={"source_sha256":expected,"returncode":p.returncode,"error_headers":errors,"stdout":p.stdout,"stderr":p.stderr,"argv":argv,"seconds":time.perf_counter()-start}
    (H/"false-source-execution.json").write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps({"returncode":p.returncode,"error_count":len(errors),"seconds":out["seconds"]}))
    assert p.returncode!=0 and len(errors)==5
if __name__=="__main__":main()
