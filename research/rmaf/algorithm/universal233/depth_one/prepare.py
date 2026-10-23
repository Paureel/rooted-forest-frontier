#!/usr/bin/env python3
"""One-shot extension of completed source-cut stack for depth-one proofs."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[4];U=D.parent
specs=[('RMAF',R/'research/rmaf/lean/RMAF.lean')]
for directory,names in [
 ('geometry',['Geometry','Bridge','Composition']),
 ('core',['CoreGraph','CherryCoarsening','CoreProgram','CoreInvariants']),
 ('integration',['SourceBridge','Contraction','Normalization','InitialLift','Suppression','EraseLift','Origins','Branches','CutRecords']),
 ('cut_realization',['OriginalGraph','Display','Regions','History','Realization','OwnerCover','Coverage','InitialCoverage','Cost','ValidPartition']),
 ('restriction_bridge',['Restriction','Embedding','Partition'])]:
 specs += [(n,U/directory/(n+'.lean')) for n in names]
B=D/'build';B.mkdir(exist_ok=True)
entries=[]
for n,p in specs:
 data=p.read_bytes();(B/(n+'.lean')).write_bytes(data)
 entries.append({'module':n,'path':str(p.relative_to(R)),'sha256':hashlib.sha256(data).hexdigest()})
(D/'STACK-PINS.json').write_text(json.dumps({'entries':entries},indent=2)+'\n')
print(' '.join(n for n,_ in specs))
