#!/usr/bin/env python3
"""One-shot supplemental source/twin audit for this review only.
The original negative statements are retained; each logical negation is checked
as a positive twin. Nested Lean comments are removed before forbidden-token scan.
"""
from pathlib import Path
import json,re,hashlib,os,subprocess,time
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((HERE/'rebuild-receipt.json').read_text())
d=json.loads((ROOT/'research/rmaf/bridge_review/degree_two/FINAL-REPLAY.json').read_text())
a=json.loads((ROOT/d['receipt']).read_text())
old=json.loads((ROOT/'research/rmaf/bridge_review/leastness/acceptance.json').read_text())
inputs=HERE/'inputs'; inputs.mkdir(exist_ok=True)
twins=HERE/'twins'; twins.mkdir(exist_ok=True)

def no_comments(s):
 out=[]; i=0; depth=0
 while i<len(s):
  if s.startswith('/-',i):depth+=1;i+=2
  elif depth and s.startswith('-/',i):depth-=1;i+=2
  elif depth:i+=1
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:out.append(s[i]);i+=1
 assert not depth
 return ''.join(out)
scan=[]
for p,h in a['source_pins'].items():
 s=ROOT/p; text=no_comments(s.read_text())
 forbidden=re.findall(r'\b(?:axiom|sorry|admit|native_decide|unsafe|implemented_by)\b',text)
 assert not forbidden,(p,forbidden)
 if p in old['source_hashes']:assert h==old['source_hashes'][p]
 scan.append(dict(source=p,sha256=sha(s),imports=re.findall(r'^import (.+)$',text,re.M),forbidden_tokens=forbidden,prior_checkpoint_pin=p in old['source_hashes']))
env=os.environ.copy();env['LEAN_PATH']=str(HERE/'isolated')
controls=[]
for row in r['builds']:
 src=ROOT/row['source']; preserve=inputs/(row['name']+'.lean');preserve.write_bytes(src.read_bytes())
 assert sha(preserve)==row['source_sha256']
 if not row.get('explicit_false'):continue
 text=src.read_text(); before,tail=text.split('example : ',1);prop,after=tail.split(' := by decide',1)
 assert not after.strip()
 twin=twins/(row['name']+'.lean');twin.write_text(before+'example : ¬ ('+prop+') := by decide\n')
 start=time.perf_counter();run=subprocess.run([str(ROOT/'bootloops-lean'),str(twin)],cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=60)
 log=HERE/'logs'/('twin-'+row['name']+'.log');log.write_text(run.stdout)
 assert run.returncode==0,(row['name'],run.stdout)
 controls.append(dict(name=row['name'],false_source_sha256=sha(preserve),twin=str(twin.relative_to(ROOT)),twin_sha256=sha(twin),log=str(log.relative_to(ROOT)),log_sha256=sha(log),exit_code=run.returncode,seconds=time.perf_counter()-start))
assert len(controls)==16
out=dict(status='pass',source_scan=scan,semantic_twins=controls,source_snapshots=str(inputs.relative_to(ROOT)),previous_checkpoint_hashes_match=True,script_sha256=sha(Path(__file__)))
(HERE/'audit-receipt.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status='pass',source_files=len(scan),positive_twins=len(controls),forbidden_tokens=0)))
