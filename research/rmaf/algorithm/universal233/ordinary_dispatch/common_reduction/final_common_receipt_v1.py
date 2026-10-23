from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/'results/algorithm-universal233-ordinary-common-reduction-20261015T185752074314Z';P=R/'results/algorithm-universal233-ordinary-source-pool-20261015T144445575127Z'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
x=json.loads((B/'development-controls-v1.json').read_text());assert x['status']=='PASS_AUTHOR_LITERAL_COMMON_CONTROLS';order=[];seen=set()
def visit(n):
 if n in seen:return
 p=B/(n+'.lean');assert p.exists()
 for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
  if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
 seen.add(n);order.append(n)
visit('CommonControls');rows=[]
for n in order:
 p=B/(n+'.lean');o=B/(n+'.olean');assert o.exists();origin='FRESH_COMMON_SOURCE_BUILD'
 if (P/p.name).exists() and sha(P/p.name)==sha(p):assert sha(P/o.name)==sha(o);origin='UNCHANGED_COMPLETED_SOURCE_AND_BINARY'
 rows.append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),olean_sha256=sha(o),mode=origin))
for n in ['CommonDispatch','CommonControls']:assert sha(D/(n+'.lean'))==sha(B/(n+'.lean'))
rec=dict(status='PASS_AUTHOR_COMMON_SOURCE_CLOSURE_WITH_LITERAL_CONTROLS',all_main_milestones='OPEN',independent_acceptance=False,source_entries=rows,source_modules=len(rows),fresh_modules=sum(e['mode']=='FRESH_COMMON_SOURCE_BUILD' for e in rows),qualified_reuse='Remaining modules are exact pinned completed source AND binary, relocated into one import root, not described as fresh rebuilds.',controls_receipt_sha256=sha(B/'development-controls-v1.json'),initial_failed_staging_sha256=sha(B/'certificate.json'),runtime='OPEN',full_ordinary_solver=False)
(B/'final-source-receipt-v1.json').write_text(json.dumps(rec,indent=2)+'\n');print('FINAL',len(rows),rec['fresh_modules'])
