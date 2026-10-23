#!/usr/bin/env python3
"""One-shot development adapter; final evidence is produced by replay.py."""
from pathlib import Path
import os, shutil, subprocess, time
H=Path(__file__).resolve().parent
R=H.parents[4]
B=H.parent
OUT=H/'build'
S=[('RMAF',R/'research/rmaf/lean/RMAF.lean')]
S += [(n,B/'geometry'/(n+'.lean')) for n in ('Geometry','Bridge','Composition')]
S += [(n,B/'core'/(n+'.lean')) for n in ('CoreGraph','CherryCoarsening','CoreProgram','CoreInvariants')]
S += [(n,B/'integration'/(n+'.lean')) for n in ('SourceBridge','Contraction','Normalization','InitialLift','Suppression','EraseLift','Origins','Branches','CutRecords')]
S += [('OriginalGraph',B/'cut_realization/OriginalGraph.lean')]
S += [(n,H/(n+'.lean')) for n in ('Executable','Endpoint','Restriction','PendantExclusion','Refinement','Components','Safety','Controls')]
for n,p in S:
    dst=OUT/p.name
    changed=not dst.exists() or dst.read_bytes()!=p.read_bytes()
    if changed: shutil.copyfile(p,dst)
    if changed or not (OUT/(n+'.olean')).exists():
        start=time.monotonic()
        q=subprocess.run([str(R/'bootloops-lean'),'-o',str(OUT/(n+'.olean')),str(dst)],cwd=OUT,env=dict(os.environ,LEAN_PATH=str(OUT)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
        (OUT/(n+'.log')).write_text(q.stdout)
        print(n,q.returncode,round(time.monotonic()-start,3),flush=True)
        if q.returncode:
            print(q.stdout)
            raise SystemExit(q.returncode)
