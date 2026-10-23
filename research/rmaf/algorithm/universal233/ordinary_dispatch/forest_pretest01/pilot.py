#!/usr/bin/env python3
"""Problem-specific 30s/module author Lean pilot, retaining every failure."""
from pathlib import Path
import datetime,json,os,subprocess,sys,time
D=Path(__file__).resolve().parent;R=D.parents[5]
C=R/'results/algorithm-universal233-forest-solver-20261015T114224630584Z'
O=R/'results'/('algorithm-universal233-forest-pretest01-pilot-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
O.mkdir(); rec={'status':'RUNNING','runs':[],'author_development':True,'all_main_milestones':'OPEN'}
for n in sys.argv[1:]:
 start=time.monotonic();env=dict(os.environ,LEAN_PATH=str(C)+':'+str(D))
 try:
  p=subprocess.run([str(R/'bootloops-lean'),'-o',str(D/(n+'.olean')),str(D/(n+'.lean'))],cwd=R,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
  code=p.returncode;out=p.stdout
 except subprocess.TimeoutExpired as e:code=124;out=str(e.stdout or '')+'\nPILOT_TIMEOUT_30S\n'
 (O/(n+'.log')).write_text(out);rec['runs'].append({'module':n,'exit':code,'seconds':time.monotonic()-start})
 (O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n');print(n,code,out[-5000:],flush=True)
 if code:rec['status']='FAIL_RETAINED';(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n');print(O);sys.exit(code)
rec['status']='PASS_AUTHOR_PILOT';(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n');print(O)
