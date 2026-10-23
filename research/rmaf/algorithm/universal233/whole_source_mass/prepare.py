#!/usr/bin/env python3
"""One-shot isolated frozen-source build for this problem-specific Lean proof."""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
BASE=HERE.parent
OUT=HERE/'build'
OUT.mkdir(exist_ok=True)
manifest=json.loads((BASE/'source_coverage/SOURCE-COVERAGE-MANIFEST-v1.json').read_text())
for item in manifest['immutable_files']:
    p=ROOT/item['path']
    assert hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256'],str(p)
SPECS=[('RMAF',ROOT/'research/rmaf/lean/RMAF.lean')]
SPECS += [(n,BASE/'geometry'/(n+'.lean')) for n in ['Geometry','Bridge','Composition']]
SPECS += [(n,BASE/'core'/(n+'.lean')) for n in ['CoreGraph','CherryCoarsening','CoreProgram','CoreInvariants']]
SPECS += [(n,BASE/'integration'/(n+'.lean')) for n in ['SourceBridge','Contraction','Normalization','InitialLift','Suppression','EraseLift','Origins','Branches','CutRecords']]
SPECS += [(n,BASE/'source_coverage'/(n+'.lean')) for n in ['FullTransport','Coverage','Entrypoint','OutputBudget','ColorBudget','ColorSteps','RawMass','RationalMass']]
env=dict(os.environ,LEAN_PATH=str(OUT))
records=[]
for n,p in SPECS:
    (OUT/(n+'.lean')).write_bytes(p.read_bytes())
    start=time.monotonic()
    r=subprocess.run([str(ROOT/'bootloops-lean'),'-o',str(OUT/(n+'.olean')),str(OUT/(n+'.lean'))],cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
    (OUT/(n+'.log')).write_text(r.stdout)
    records.append({'module':n,'seconds':time.monotonic()-start,'code':r.returncode,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
    assert r.returncode==0,(n,r.stdout)
(OUT/'prepare.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({'modules':len(records),'seconds':sum(r['seconds'] for r in records),'status':'PASS_SOURCE_IMPORT_PILOT'}))
