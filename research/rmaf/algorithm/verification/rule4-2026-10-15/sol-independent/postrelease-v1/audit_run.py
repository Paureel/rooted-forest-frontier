"""One-shot bounded execution of the unchanged frozen producer instrument.

Each producer is audited separately to bound memory. Exact stdout is streamed to
gzip; no source/body expression is truncated or replaced by a mere count/hash.
Postcontact driver uses the precontact Lean auditor unchanged.
"""
import argparse,gzip,hashlib,json,os,pathlib,signal,subprocess,time,threading,traceback
H=pathlib.Path(__file__).resolve().parent; PRE=H.parent
ROOT=next(p for p in H.parents if(p/"bootloops-python").exists())
REPLAY=H/"cold-source";OUT=H/"producer-audits";OUT.mkdir(exist_ok=True)
def sha(path):
    d=hashlib.sha256()
    with path.open("rb")as f:
        while b:=f.read(1024*1024):d.update(b)
    return d.hexdigest()
def audit(name):
    dest=OUT/(name+".json.gz"); meta=OUT/(name+".meta.json")
    if dest.exists()or meta.exists():raise RuntimeError("immutable audit already exists: "+name)
    env=os.environ.copy();env["LEAN_PATH"]=str(REPLAY)
    argv=[str(ROOT/"bootloops-lean"),"--run",str(PRE/"ProducerAudit.lean"),name]
    t=time.perf_counter();stderr=OUT/(name+".stderr")
    d=hashlib.sha256();count=0
    with stderr.open("wb")as err,dest.open("wb")as compressed:
        proc=subprocess.Popen(argv,cwd=REPLAY,env=env,stdout=subprocess.PIPE,stderr=err,start_new_session=True)
        timed=[False]
        def stop():
            timed[0]=True
            if proc.poll()is None:os.killpg(proc.pid,signal.SIGKILL)
        timer=threading.Timer(30,stop);timer.start()
        try:
            with gzip.GzipFile(fileobj=compressed,mode="wb")as target:
                while chunk:=proc.stdout.read(1024*1024):
                    count+=len(chunk);d.update(chunk);target.write(chunk)
                    if count>400000000:os.killpg(proc.pid,signal.SIGKILL);raise RuntimeError("400MB producer-output cap")
            rc=proc.wait()
        finally:timer.cancel()
    result={"producer":name,"argv":argv,"returncode":rc,"timeout":timed[0],"source_sha256":sha(REPLAY/(name+".lean")),
            "auditor_sha256":sha(PRE/"ProducerAudit.lean"),"uncompressed_bytes":count,"uncompressed_sha256":d.hexdigest(),
            "gzip_bytes":dest.stat().st_size,"gzip_sha256":sha(dest),"seconds":time.perf_counter()-t,"LEAN_PATH":env["LEAN_PATH"]}
    meta.write_text(json.dumps(result,indent=2)+"\n")
    if rc or timed[0]:raise RuntimeError((name,"AUDIT_FAILED",rc,timed[0]))
    print(json.dumps({k:result[k]for k in["producer","returncode","uncompressed_bytes","seconds"]}))
def main():
    p=argparse.ArgumentParser();p.add_argument("modules",nargs="*");p.add_argument("--next",type=int);a=p.parse_args()
    modules=a.modules
    if a.next:
        dag=json.loads((H/"source-dag.json").read_text())
        modules=[n for n in dag["order"]if(REPLAY/(n+".olean")).exists()and not(OUT/(n+".meta.json")).exists()][:a.next]
    if not modules:raise RuntimeError("no requested pending compiled producers")
    for name in modules:audit(name)
if __name__=="__main__":
    try:main()
    except Exception:
        with(H/"audit-failures.log").open("a")as f:f.write(traceback.format_exc()+"\n")
        raise
