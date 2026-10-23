from pathlib import Path
import datetime,hashlib,json,os,shutil,subprocess,sys,time
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/'results/algorithm-universal233-ordinary-recursion-20261015T191007632025Z'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
n=sys.argv[1];p=D/(n+'.lean');q=B/p.name
assert not q.exists() or q.stat().st_nlink==1,'REFUSE_LINKED_DEPENDENCY_WRITE'
assert shutil.disk_usage(R).free>=3*(1<<30),'FREE_SPACE_MARGIN_STOP'
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
if q.exists():(B/(n+'-before-'+stamp+'.lean.txt')).write_bytes(q.read_bytes())
q.write_bytes(p.read_bytes());start=time.monotonic();z=subprocess.run([str(R/'bootloops-lean'),'-o',str(B/(n+'.olean')),str(q)],cwd=B,env=dict(os.environ,LEAN_PATH=str(B)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=30)
log=B/(n+'-'+stamp+'.log');log.write_text(z.stdout);rec=dict(module=n,source_sha256=sha(p),exit=z.returncode,seconds=time.monotonic()-start,log=str(log.relative_to(R)),log_sha256=sha(log));(B/(n+'-'+stamp+'-receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');print(z.stdout);print(json.dumps(rec));raise SystemExit(z.returncode)
