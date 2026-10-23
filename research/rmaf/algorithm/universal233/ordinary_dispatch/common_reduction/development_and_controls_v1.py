from pathlib import Path
import hashlib,json,os,shutil,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/'results/algorithm-universal233-ordinary-common-reduction-20261015T185752074314Z'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rec=dict(status='RUNNING_AUTHOR_COMMON_CONTROLS',pins={str(p.relative_to(R)):sha(p) for p in [Path(__file__),D/'TARGET-v1.md',D/'CONTROLS-PIN-v1.md']},runs=[])
def save():(B/'development-controls-v1.json').write_text(json.dumps(rec,indent=2)+'\n')
save()
try:
 for n,w in [('CommonDispatch',0),('CommonControls',0),('CommonFalseControls',1)]:
  assert shutil.disk_usage(R).free>=3*(1<<30),'FREE_SPACE_MARGIN_STOP';p=D/(n+'.lean');q=B/p.name;q.write_bytes(p.read_bytes());start=time.monotonic()
  z=subprocess.run([str(R/'bootloops-lean')]+(['-o',str(B/(n+'.olean'))] if w==0 else [])+[str(q)],cwd=B,env=dict(os.environ,LEAN_PATH=str(B)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=30)
  log=B/(n+'-controls-v1.log');log.write_text(z.stdout);rec['runs'].append(dict(module=n,source_sha256=sha(p),expected_exit=w,exit=z.returncode,seconds=time.monotonic()-start,log_sha256=sha(log)));save();assert z.returncode==w,(n,z.stdout);print('CONTROL',n,z.returncode,flush=True)
 assert (B/'CommonFalseControls-controls-v1.log').read_text().count('error:')==2
 rec['status']='PASS_AUTHOR_LITERAL_COMMON_CONTROLS';save()
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
