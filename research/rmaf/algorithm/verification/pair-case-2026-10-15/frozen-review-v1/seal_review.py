#!/usr/bin/env python3
"""One-shot local review snapshot; no scientific calculation or external IO."""
from pathlib import Path
import hashlib,json,shutil,os
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
RES=ROOT/'research/rmaf/results'
DEST=HERE/'frozen-review-v1'
assert not DEST.exists()
final=RES/'algorithm-pair-case-fresh-review-final-v1.json'
d=json.loads(final.read_text())
d['artifacts'].append('results/algorithm-pair-case-fresh-review-whole-B-v1.json')
d['whole_bad_B_false_control']={'all_original_source_edges':12,'actual_B_embedding_edges':6,'separating_edges':0}
d['final_snapshot']='algorithm/verification/pair-case-2026-10-15/frozen-review-v1'
d['final_manifest']='algorithm/verification/pair-case-2026-10-15/frozen-review-v1/MANIFEST.json'
final.write_text(json.dumps(d,indent=2)+'\n')
DEST.mkdir()
for p in HERE.iterdir():
    if p.is_file() and (p.suffix in ('.md','.py','.lean','.json','.jsonl') or 'SHA256SUMS' in p.name):
        shutil.copy2(p,DEST/p.name)
for name in ('frozen-readiness-v1','failed-instruments'):
    shutil.copytree(HERE/name,DEST/name,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
for p in (HERE/'isolated-review-v1').rglob('*'):
    if p.is_file() and p.suffix in ('.lean','.log','.json'):
        to=DEST/p.relative_to(HERE);to.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,to)
(DEST/'results').mkdir()
for p in RES.glob('algorithm-pair-case-fresh-review-*.json'):
    shutil.copy2(p,DEST/'results'/p.name)
files={str(p.relative_to(DEST)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(DEST.rglob('*')) if p.is_file()}
manifest={'verdict':d['verdict'],'scope':d['scope'],'file_count':len(files),'files':files,'compiled_oleans_included':False}
(DEST/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
seal=hashlib.sha256((DEST/'MANIFEST.json').read_bytes()).hexdigest()
(HERE/'FINAL-SEAL-v1.json').write_text(json.dumps({'manifest':str((DEST/'MANIFEST.json').relative_to(ROOT)),'sha256':seal,'entries':len(files)},indent=2)+'\n')
for p,h in files.items():assert hashlib.sha256((DEST/p).read_bytes()).hexdigest()==h
for p in DEST.rglob('*'):
    p.chmod(p.stat().st_mode & ~0o222)
DEST.chmod(DEST.stat().st_mode & ~0o222)
print(json.dumps({'manifest':str((DEST/'MANIFEST.json').relative_to(ROOT)),'sha256':seal,'entries':len(files),'rechecked':True}))
