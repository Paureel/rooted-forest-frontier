from pathlib import Path
import os,subprocess,time,json,hashlib
b=Path(__file__).resolve().parent;root=b.parents[4];rows=[]
for label in ['query','rank']:
 iso=b/('isolated-'+label);env=os.environ.copy();env['LEAN_PATH']=str(iso);t=time.monotonic()
 r=subprocess.run([str(root/'bootloops-lean'),'--run','ReviewActual.lean'],cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60)
 (b/('ACTUAL-'+label.upper()+'.stdout.log')).write_text(r.stdout)
 (b/('ACTUAL-'+label.upper()+'.stderr.log')).write_text(r.stderr)
 (b/('ACTUAL-'+label.upper()+'.log')).write_text(r.stderr+r.stdout)
 rows.append({'label':label,'exit':r.returncode,'seconds':time.monotonic()-t,'source_sha256':hashlib.sha256((iso/'ReviewActual.lean').read_bytes()).hexdigest(),'streams':'separate capture;combined artifact concatenates complete stderr then stdout'})
 assert r.returncode==0,(r.stdout,r.stderr)
(b/'ACTUAL-RUNS-final.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows))
