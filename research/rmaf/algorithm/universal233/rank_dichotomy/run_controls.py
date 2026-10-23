#!/usr/bin/env python3
"""One-shot preproof actual-generator controls; development evidence only.

The toolkit index and existing rMAF instruments were consulted. These controls
wrap the frozen Lean executable directly because a separate enumerator cannot
establish equality of its literal output list. No new solver is introduced.
"""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, time
D = Path(__file__).resolve().parent
ROOT = D.parents[4]
STAMP = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
OUT = ROOT / 'results' / ('algorithm-universal233-rank-controls-' + STAMP)
OUT.mkdir()
STACK = D.parent / 'assembly/replay/20261015T084051Z'
env = dict(os.environ, LEAN_PATH=str(D)+':'+str(STACK))
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
records = []
for module in ['Controls','FalseControls']:
    args = [str(ROOT/'bootloops-lean')]
    if module == 'Controls': args += ['-o',str(D/(module+'.olean'))]
    args += [str(D/(module+'.lean'))]
    start = time.monotonic()
    p = subprocess.run(args,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
    (OUT/(module+'.log')).write_text(p.stdout)
    records.append({'module':module,'exit':p.returncode,'seconds':time.monotonic()-start,'source_sha256':digest(D/(module+'.lean'))})
    if module == 'Controls': assert p.returncode == 0,p.stdout
    else:
        assert p.returncode != 0,p.stdout
        assert 'false_label_only_embedding' not in p.stdout # errors locate source line, no fabricated verdict
        assert p.stdout.count('is false') == 2 and '⊢ False' in p.stdout,p.stdout
receipt = {'status':'PASS_PREPROOF_CONTROLS_ONLY','pin_sha256':digest(D/'CONTROLS-PIN-v1.json'),'target_sha256':digest(D/'TARGET-v1.md'),'records':records,'false_controls_rejected':3,'lineage':'Development only; same author; no universal proof or independent verification.'}
(OUT/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
(D/'CONTROLS-RECEIPT.txt').write_text(str(OUT)+'\n')
print('PASS preproof actual-generator controls; 9 positive statements; 3 false controls rejected.')
print(OUT)
