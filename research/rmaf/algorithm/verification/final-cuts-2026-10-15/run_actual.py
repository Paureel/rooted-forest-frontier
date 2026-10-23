from pathlib import Path
import os,subprocess,time,json,hashlib
b=Path(__file__).resolve().parent;root=b.parents[4];iso=b/'isolated';env=os.environ.copy();env['LEAN_PATH']=str(iso);start=time.monotonic()
r=subprocess.run([str(root/'bootloops-lean'),'--run','ReviewActual.lean'],cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60)
(b/'ACTUAL.stdout.log').write_text(r.stdout);(b/'ACTUAL.stderr.log').write_text(r.stderr)
out={'exit':r.returncode,'seconds':time.monotonic()-start,'source_sha256':hashlib.sha256((iso/'ReviewActual.lean').read_bytes()).hexdigest(),'stdout_sha256':hashlib.sha256(r.stdout.encode()).hexdigest(),'stderr_sha256':hashlib.sha256(r.stderr.encode()).hexdigest(),'streams':'separate; no interleaved JSON','traced_colors':'separate diagnostic generate with same blockColor value, not an effect trace of hardcoded recover'}
(b/'ACTUAL-RUN.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));assert r.returncode==0,(r.stdout,r.stderr)
