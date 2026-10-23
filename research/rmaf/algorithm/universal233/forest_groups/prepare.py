#!/usr/bin/env python3
"""One-shot local source adaptation. No mathematical expected output generation."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
BASE=HERE.parent
OUT=HERE/'build'
OUT.mkdir(exist_ok=True)
SPECS=[('RMAF',ROOT/'research/rmaf/lean/RMAF.lean',{}),
 ('GroupRestriction',BASE/'restriction_bridge/Restriction.lean',{}),
 ('GroupEmbedding',BASE/'restriction_bridge/Embedding.lean',{'Restriction':'GroupRestriction'}),
 ('GroupPartition',BASE/'restriction_bridge/Partition.lean',{'Embedding':'GroupEmbedding'}),
 ('GroupCost',BASE/'restriction_bridge/Cost.lean',{'Partition':'GroupPartition'}),
 ('GroupForward',BASE/'restriction_bridge/Forward.lean',{'Cost':'GroupCost'}),
 ('Geometry',BASE/'geometry/Geometry.lean',{}),
 ('Bridge',BASE/'geometry/Bridge.lean',{}),
 ('Composition',BASE/'geometry/Composition.lean',{}),
 ('GroupReconstruction',BASE/'restriction_bridge/Reconstruction.lean',{'Forward':'GroupForward'}),
 ('GroupState',BASE/'state_reductions/State.lean',{'StatePartition':'GroupPartition'}),
 ('GroupStateFacts',BASE/'state_reductions/Singleton.lean',{'State':'GroupState'})]
records=[]
for name,path,adapts in SPECS:
 text=path.read_text()
 for old,new in adapts.items():
  assert text.count('import '+old+'\n')==1
  text=text.replace('import '+old+'\n','import '+new+'\n',1)
 (OUT/(name+'.lean')).write_text(text)
 records.append(dict(module=name,path=str(path.relative_to(ROOT)),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),adaptations=adapts,adapted_sha256=hashlib.sha256(text.encode()).hexdigest()))
(OUT/'lean-toolchain').write_bytes((BASE/'integration/lean-toolchain').read_bytes())
(HERE/'STACK-PINS.json').write_text(json.dumps(dict(entries=records),indent=2)+'\n')
