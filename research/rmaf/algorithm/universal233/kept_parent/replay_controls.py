#!/usr/bin/env python3
"""One-shot isolated literal-core replay of frozen kept-parent controls."""
from pathlib import Path
import hashlib,json,os,subprocess,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];BASE=HERE.parent
OUT=HERE/'build';OUT.mkdir(exist_ok=True)
SPECS=[('RMAF',ROOT/'research/rmaf/lean/RMAF.lean'),('CoreGraph',BASE/'core/CoreGraph.lean'),('CoreProgram',BASE/'core/CoreProgram.lean')]
env=dict(os.environ,LEAN_PATH=str(OUT));records=[]
for n,p in SPECS:
 (OUT/(n+'.lean')).write_bytes(p.read_bytes());start=time.monotonic()
 r=subprocess.run([str(ROOT/'bootloops-lean'),'-o',str(OUT/(n+'.olean')),str(OUT/(n+'.lean'))],env=env,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 (OUT/(n+'.log')).write_text(r.stdout);records.append({'module':n,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'returncode':r.returncode})
 assert not r.returncode,(n,r.stdout)
start=time.monotonic()
r=subprocess.run([str(ROOT/'bootloops-lean'),'--run',str(HERE/'LiteralControls.lean')],env=env,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60)
(HERE/'literal-controls.jsonl').write_text(r.stdout);(HERE/'literal-controls-stderr.log').write_text(r.stderr)
assert not r.returncode,r.stderr
actual=[json.loads(s) for s in r.stdout.splitlines()]
expected=json.loads((ROOT/'research/rmaf/results/algorithm-universal233-kept-controls-v1.json').read_text())['rows']
assert len(actual)==len(expected)==90
for a,e in zip(actual,expected):
 assert all(a[k]==e[k] for k in ['id','q','source_partition','source_embeddings']),(a,e)
 assert all(a[k]==e['receipt'][k] for k in ['outputs','refusals','visited','childAttempts','pruned']),(a,e)
result={'schema':'universal233-kept-literal-replay/v1','matched_configs':len(actual),'literal_output_count':sum(len(a['outputs']) for a in actual),'replay_seconds':time.monotonic()-start,'source_modules':records,'development_comparison_only':True,'all_main_milestones':'OPEN'}
(ROOT/'research/rmaf/results/algorithm-universal233-kept-literal-controls-v1.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
