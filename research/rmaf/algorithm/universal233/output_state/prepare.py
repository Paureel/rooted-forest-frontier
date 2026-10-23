#!/usr/bin/env python3
"""One-shot output-state Lean source adapter. Toolkit index consulted: none of its
numerical tools implement literal rooted-MAF Lean forests. Wrap completed frozen
source modules, with import-only changes and full source/adapted hashes.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[4];U=D.parent;B=D/'build';B.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
S=[]
for mod,sub,filename,ad in [
 ('RMAF','','',{}),('GroupRestriction','restriction_bridge','Restriction',{}),
 ('GroupEmbedding','restriction_bridge','Embedding',{'Restriction':'GroupRestriction'}),
 ('GroupPartition','restriction_bridge','Partition',{'Embedding':'GroupEmbedding'}),
 ('GroupCost','restriction_bridge','Cost',{'Partition':'GroupPartition'}),
 ('GroupForward','restriction_bridge','Forward',{'Cost':'GroupCost'}),
 ('Geometry','geometry','Geometry',{}),('Bridge','geometry','Bridge',{}),('Composition','geometry','Composition',{}),
 ('GroupReconstruction','restriction_bridge','Reconstruction',{'Forward':'GroupForward'}),
 ('GroupState','state_reductions','State',{'StatePartition':'GroupPartition'}),
 ('GroupStateFacts','state_reductions','Singleton',{'State':'GroupState'}),
 ('GroupDefs','forest_groups','GroupDefs',{}),('GroupForwardProof','forest_groups','GroupForwardProof',{}),
 ('GroupReverseProof','forest_groups','GroupReverseProof',{}),('GroupCostProof','forest_groups','GroupCostProof',{}),
 ('GroupPriority','forest_groups','GroupPriority',{})]:
 p=R/'research/rmaf/lean/RMAF.lean' if mod=='RMAF' else U/sub/(filename+'.lean');S.append((mod,p,ad))
# Frozen prerequisite sources are read-only development contacts.
manifest_paths=[U/'restriction_bridge/RESTRICTION-MANIFEST-v1.json',U/'state_reductions/STATE-MANIFEST-v1.json',U/'forest_groups/FOREST-GROUPS-MANIFEST-v2.json']
checks=[]
for p in manifest_paths:
 m=json.loads(p.read_text());rows=m.get('immutable_files',m.get('entries',[]));assert rows
 for e in rows:assert sha(R/e['path'])==e['sha256'],e['path']
 checks.append({'path':str(p.relative_to(R)),'sha256':sha(p),'checked':len(rows)})
entries=[];runs=[]
for n,p,ad in S:
 data=p.read_text()
 for old,new in ad.items():
  assert data.count('import '+old+'\n')==1;data=data.replace('import '+old+'\n','import '+new+'\n',1)
 q=B/(n+'.lean');q.write_text(data)
 entries.append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),adaptations=ad,adapted_sha256=sha(q)))
(B/'lean-toolchain').write_bytes((R/'research/rmaf/lean/lean-toolchain').read_bytes())
for n,_,_ in S:
 t=time.monotonic();p=subprocess.run([str(R/'bootloops-lean'),'-o',str(B/(n+'.olean')),str(B/(n+'.lean'))],cwd=B,env=dict(os.environ,LEAN_PATH=str(B)),capture_output=True,text=True,timeout=60)
 (B/(n+'.log')).write_text(p.stdout+p.stderr);runs.append(dict(module=n,exit=p.returncode,seconds=time.monotonic()-t));assert p.returncode==0,(n,p.stdout,p.stderr)
(D/'STACK-PINS.json').write_text(json.dumps(dict(development_only=True,manifests=checks,entries=entries,runs=runs),indent=2)+'\n')
print('Prepared',len(S),'completed modules in',round(sum(x['seconds'] for x in runs),3),'seconds')
