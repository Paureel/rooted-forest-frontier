#!/usr/bin/env python3
"""One-shot measured subprocess evidence runner; no candidate discovery."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--out",required=True)
    p.add_argument("--cwd",default=".")
    p.add_argument("--timeout",type=float,default=60)
    p.add_argument("command",nargs=argparse.REMAINDER)
    a=p.parse_args()
    command=a.command[1:] if a.command[:1]==["--"] else a.command
    out=Path(a.out)
    if out.exists():
        raise RuntimeError("refuse evidence overwrite")
    before=shutil.disk_usage(out.parent).free
    if before<3*2**30:
        raise RuntimeError("3 GiB free-space floor")
    start=time.perf_counter()
    result={"command":command,"cwd":str(Path(a.cwd).resolve()),"timeout_seconds":a.timeout,
            "disk_free_before":before}
    try:
        process=subprocess.run(command,cwd=a.cwd,text=True,capture_output=True,timeout=a.timeout)
        result.update(exit_code=process.returncode,stdout=process.stdout,stderr=process.stderr,
                      status="PASS" if process.returncode==0 else "FAIL")
    except subprocess.TimeoutExpired as error:
        result.update(status="TIMEOUT",stdout=str(error.stdout or ""),stderr=str(error.stderr or ""))
    result["seconds"]=time.perf_counter()-start
    result["disk_free_after"]=shutil.disk_usage(out.parent).free
    out.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:result[k] for k in ("status","seconds","disk_free_after")} | {"receipt":str(out)}))
    return 0 if result["status"]=="PASS" else 1

if __name__=="__main__":
    raise SystemExit(main())
