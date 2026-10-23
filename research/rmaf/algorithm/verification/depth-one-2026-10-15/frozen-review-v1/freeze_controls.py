#!/usr/bin/env python3
"""Metadata-only freeze before first mathematical or Std toy execution."""
from pathlib import Path
import json,hashlib,shutil,datetime
H=Path(__file__).resolve().parent;ROOT=next(p for p in H.parents if (p/'bootloops-python').is_file());D=H/'frozen-controls-v1';assert not D.exists();D.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files=['TARGET-v1.md','README.md','METHOD-v1.md','CONTROL-PIN-v1.json','LEAN-GATES-v1.json','independent_depth_one.py','std_toy_gates.py','freeze_controls.py']
for n in files:shutil.copy2(H/n,D/n)
deps=[('research/rmaf/lean/RMAF.lean','4960d5be9a5f1eb6b15d11c76130bee5263125631314a4eb2d43d500d5b513a9'),('research/rmaf/algorithm/verification/pair-case-2026-10-15/frozen-readiness-v1/independent_paircase.py','9f9d9d33ddcfe867a9d82113478a07807f1ad73b32cf50c3180aa54a6770eab4')]
for p,w in deps:assert sha(ROOT/p)==w
manifest={'phase':'PRE-CANDIDATE; before any control execution','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':{n:sha(D/n) for n in files},'dependencies':[{'path':p,'sha256':w} for p,w in deps],'candidate_contacts':0,'extra_replications':0,'all_main_milestones':'OPEN'}
(D/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
for p in D.iterdir():p.chmod(p.stat().st_mode & ~0o222)
D.chmod(D.stat().st_mode & ~0o222)
seal={'manifest':str((D/'MANIFEST.json').relative_to(ROOT)),'sha256':sha(D/'MANIFEST.json'),'entries':len(files),'candidate_contacts':0}
(H/'CONTROLS-SEAL-v1.json').write_text(json.dumps(seal,indent=2)+'\n');print(json.dumps(seal))
