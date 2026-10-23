#!/usr/bin/env python3
"""One-shot pinned actual original-tree preproof controls, not a census."""
from pathlib import Path
import hashlib,datetime,subprocess,os,json,time
D=Path(__file__).resolve().parent; R=D.parents[4]
O=R/'results'/('algorithm-universal233-cherry-branch-pre-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')); O.mkdir()
inputs=[R/'research/rmaf/lean/RMAF.lean',D.parent/'hard_parent_refinement/Executable.lean',D/'PreControls.lean',D/'FalsePreControls.lean',D/'CONTROLS-PIN.md',D/'TARGET-v1.md',Path(__file__),D/'lean-toolchain']
hashes={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
for p in inputs:(O/p.name).write_bytes(p.read_bytes())
record=dict(status='RUNNING',source_hashes=hashes,runs=[])
for n in ['RMAF','Executable','PreControls','FalsePreControls']:
 t=time.monotonic();p=subprocess.run([str(R/'bootloops-lean')]+(['-o',str(O/(n+'.olean'))] if n!='FalsePreControls' else [])+[str(O/(n+'.lean'))],cwd=O,env=dict(os.environ,LEAN_PATH=str(O)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 (O/(n+'.log')).write_text(p.stdout);record['runs'].append(dict(module=n,exit=p.returncode,seconds=time.monotonic()-t))
 (O/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
 assert (p.returncode==0 if n!='FalsePreControls' else p.returncode!=0 and p.stdout.count('is false')==5),(n,p.stdout)
record.update(status='PASS_PREPROOF',actual_true_controls=15,false_controls_rejected=5,meaning='Development preproof actual source controls; no universal theorem or independent certification')
(O/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
(D/'PREPROOF-RECEIPT-v1.json').write_text(json.dumps(dict(receipt=str(O.relative_to(R)),sha256=hashlib.sha256((O/'certificate.json').read_bytes()).hexdigest(),source_hashes=hashes),indent=2)+'\n')
print('PASS_PREPROOF: 15 actual controls; 5 false controls rejected');print(O)
