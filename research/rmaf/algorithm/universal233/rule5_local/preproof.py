#!/usr/bin/env python3
"""One-shot exact fixture/control receipt; no production graph theorem run."""
from pathlib import Path
import subprocess,json,datetime,hashlib,os,time
D=Path(__file__).resolve().parent;R=D.parents[4]
O=R/'results'/('algorithm-universal233-rule5-local-pre-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir()
pins={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
 [D/n for n in ['TARGET-v1.md','CONTROLS-PIN-v1.md','local.py','Rule5Defs.lean','Rule5PreControls.lean','Rule5FalsePreControls.lean','generate_pre.py','preproof.py']]+[R/'research/rmaf/oracle/oracle.py']}
runs=[]
for name,cmd,want in [
 ('fixture-clean',[str(R/'bootloops-python'),str(D/'local.py'),str(O/'fixture.json')],0),
 ('fixture-corruption',[str(R/'bootloops-python'),str(D/'local.py'),str(O/'bad.json'),'--corrupt'],1),
 ('lean-clean',[str(R/'bootloops-lean'),str(D/'Rule5PreControls.lean')],0),
 ('lean-false',[str(R/'bootloops-lean'),str(D/'Rule5FalsePreControls.lean')],1)]:
 t=time.monotonic();p=subprocess.run(cmd,cwd=R,env=dict(os.environ,LEAN_PATH=str(D/'build')),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
 (O/(name+'.log')).write_text(p.stdout);assert p.returncode==want,(name,p.stdout)
 if name=='fixture-corruption':assert 'EXPECTED_CLASSIFICATION' in p.stdout
 if name=='lean-false':assert p.stdout.count('is false')==4
 runs.append(dict(name=name,exit=p.returncode,seconds=time.monotonic()-t))
record=dict(status='PASS_PREPROOF_DEVELOPMENT',fixture_count=7,lean_false_rejected=4,corruption_caught=1,pins=pins,runs=runs,
 meaning='Actual original-tree fixtures and controls precede production graph proof; shared author/oracle source prevents independent certification')
(O/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
(D/'PREPROOF-RECEIPT-v1.json').write_text(json.dumps(dict(receipt=str(O.relative_to(R)),sha256=hashlib.sha256((O/'certificate.json').read_bytes()).hexdigest()),indent=2)+'\n')
print(record['status'],O)
