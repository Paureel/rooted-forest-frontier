#!/usr/bin/env python3
"""One-shot isolated source-bound dependency build for kept-parent proof."""
from pathlib import Path
import hashlib,json,os,subprocess,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];BASE=HERE.parent
OUT=HERE/'proof-build';OUT.mkdir(exist_ok=True)
SPECS=[('RMAF',ROOT/'research/rmaf/lean/RMAF.lean')]
SPECS += [(n,BASE/'geometry'/(n+'.lean')) for n in ['Geometry','Bridge','Composition']]
SPECS += [(n,BASE/'core'/(n+'.lean')) for n in ['CoreGraph','CherryCoarsening','CoreProgram','CoreInvariants']]
SPECS += [(n,BASE/'integration'/(n+'.lean')) for n in ['SourceBridge','Contraction','Normalization','InitialLift','Suppression','EraseLift','Origins','Branches','CutRecords']]
SPECS += [(n,BASE/'source_coverage'/(n+'.lean')) for n in ['FullTransport','Coverage','Entrypoint','OutputBudget','ColorBudget','ColorSteps','RawMass','RationalMass']]
SPECS += [('ParentColors',BASE/'assembly/ParentColors.lean')]
SPECS += [(('CutCoverage' if n=='Coverage' else n),BASE/'cut_realization'/(n+'.lean')) for n in ['OriginalGraph','Display','Regions','History','Realization','OwnerCover','Coverage','InitialCoverage','Cost','ValidPartition']]
env=dict(os.environ,LEAN_PATH=str(OUT));records=[]
for n,p in SPECS:
 data=p.read_bytes()
 if n=='InitialCoverage':
  assert data.startswith(b'import Coverage\n');data=data.replace(b'import Coverage\n',b'import CutCoverage\n',1)
 (OUT/(n+'.lean')).write_bytes(data);start=time.monotonic()
 r=subprocess.run([str(ROOT/'bootloops-lean'),'-o',str(OUT/(n+'.olean')),str(OUT/(n+'.lean'))],env=env,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 (OUT/(n+'.log')).write_text(r.stdout);records.append({'module':n,'source':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'returncode':r.returncode})
 (OUT/'prepare.json').write_text(json.dumps(records,indent=2)+'\n')
 assert not r.returncode,(n,r.stdout)
print(json.dumps({'modules':len(records),'seconds':sum(r['seconds'] for r in records),'status':'DEPENDENCIES_BUILT'}))
