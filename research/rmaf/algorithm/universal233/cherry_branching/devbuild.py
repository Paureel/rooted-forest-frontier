#!/usr/bin/env python3
"""One-shot development compilation of unchanged declared hard-parent contacts."""
from pathlib import Path
import subprocess,os,json,hashlib,time
D=Path(__file__).resolve().parent;R=D.parents[4];U=D.parent;O=D/'build';O.mkdir(exist_ok=True)
if (D/'CHERRY-BRANCH-MANIFEST-v1.json').exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
base=[('RMAF',R/'research/rmaf/lean/RMAF.lean')]
for dr,ns in [('geometry',['Geometry','Bridge','Composition']),('core',['CoreGraph','CherryCoarsening','CoreProgram','CoreInvariants']),('integration',['SourceBridge','Contraction','Normalization','InitialLift','Suppression','EraseLift','Origins','Branches','CutRecords']),('cut_realization',['OriginalGraph']),('hard_parent_refinement',['Executable','Endpoint','Restriction','PendantExclusion','Refinement','Components','Safety'])]:
 base += [(n,U/dr/(n+'.lean')) for n in ns]
# Completed output-state and state-cherry development contacts. Imports are
# aliased only to avoid basename collisions; declarations keep actual origins.
entries=[dict(module=n,path=str(p.relative_to(R)),adaptations={}) for n,p in base]
seen={e['module'] for e in entries}
for e in json.loads((U/'output_state/STACK-PINS.json').read_text())['entries']:
 if e['module'] not in seen:entries.append(e);seen.add(e['module'])
for n in ['OutputDefs','Materialize','Equivalence']:
 entries.append(dict(module=n,path=str((U/'output_state'/(n+'.lean')).relative_to(R)),adaptations={}))
alias={'StateRestriction':'GroupRestriction','StateEmbedding':'GroupEmbedding','StatePartition':'GroupPartition','State':'GroupState','Singleton':'GroupStateFacts','Removal':'CherryRemoval','Forward':'CherryForward','LeafClear':'CherryLeafClear','Reverse':'CherryReverse','Endpoint':'CherryEndpoint','Replacement':'CherryReplacement'}
for n in ['Removal','Forward','LeafClear','Reverse','CherryGraph','CherryTopology']:
 entries.append(dict(module=alias.get(n,n),path='results/algorithm-universal233-state-20261015T094847Z/'+n+'.lean',adaptations=alias))
for n in ['Endpoint','Replacement']:
 entries.append(dict(module=alias[n],path=str((U/'state_cherry_completion'/(n+'.lean')).relative_to(R)),adaptations=alias))
for n in ['ExchangeRestriction','Cluster','Descendant','Forest','Surgery','Count']:
 entries.append(dict(module=n,path='results/algorithm-universal233-binary-cheap-20261015T104014Z/'+n+'.lean',adaptations={}))
local=['Ordinary','Partition','Selector','Endpoints','Consumer','Priority','SourceBranches','CoreCherry','PreControls','T1Split','T1Exchange','T1Boundary','Budget','Unordered','Controls']
entries += [dict(module=n,path=str((D/(n+'.lean')).relative_to(R)),adaptations={}) for n in local]
assert len(entries)==len({e['module'] for e in entries})
(O/'lean-toolchain').write_bytes((D/'lean-toolchain').read_bytes())
for e in entries:
 n=e['module'];p=R/e['path'];src=p.read_text();e['sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
 for old,new in e['adaptations'].items():src=src.replace('import '+old+'\n','import '+new+'\n')
 e['adapted_sha256']=hashlib.sha256(src.encode()).hexdigest()
 target=O/(n+'.lean');changed=not target.exists() or target.read_text()!=src;target.write_text(src)
 (D/'DEV-STACK.json').write_text(json.dumps(entries,indent=2)+'\n')
 if not changed and (O/(n+'.olean')).exists():continue
 t=time.monotonic();q=subprocess.run([str(R/'bootloops-lean'),'-o',str(O/(n+'.olean')),str(target)],cwd=O,env=dict(os.environ,LEAN_PATH=str(O)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 (O/(n+'.log')).write_text(q.stdout)
 print(n,q.returncode,round(time.monotonic()-t,3))
 if q.returncode:print(q.stdout);raise SystemExit(q.returncode)
