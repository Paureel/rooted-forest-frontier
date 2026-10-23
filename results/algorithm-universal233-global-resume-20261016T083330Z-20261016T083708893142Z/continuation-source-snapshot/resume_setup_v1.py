# One-shot continuation receipt and exact source seed, not independent replication.
from pathlib import Path
import datetime, hashlib, json, os, shutil

D = Path(__file__).resolve().parent
R = D.parents[6]
T = R / 'research/rmaf/monitoring/resume-20261016T083330Z/global-TARGET-v1.json'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(T) == '7f6447681ad1ffe4f98acdf7ee1b6120f713afcef701d66edc05b91b7079d30b'
t = json.loads(T.read_text())
assert shutil.disk_usage(R).free >= 3*(1<<30)
B = R/'results'/('algorithm-universal233-global-resume-20261016T083330Z-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
B.mkdir()
P = R/json.loads((D.parent/'LATEST-BUILD-v1.json').read_text())['directory']
s = json.loads((P/'SEED-RECEIPT.json').read_text())
assert s['status'] == 'PASS_EXACT_READONLY_SOURCE_SEED'
rec = dict(status='CHECKING', target=str(T.relative_to(R)),target_sha256=sha(T),
    previous_build=str(P.relative_to(R)),previous_seed_sha256=sha(P/'SEED-RECEIPT.json'),
    independent_acceptance=False,all_main_milestones='OPEN',checkpoints=[],sources=[],own_completed=[])
def save(): (B/'RESUME-SEED-RECEIPT.json').write_text(json.dumps(rec,indent=2)+'\n')
save()
for e in t['own_checkpoint_sha256']:
    p=R/e['path']; assert sha(p)==e['sha256']
    rec['checkpoints'].append(e)
for e in s['sources']:
    for suffix,key in [('.lean','source_sha256'),('.olean','olean_sha256')]:
        p=P/(e['module']+suffix); assert sha(p)==e[key]
        assert not p.stat().st_mode & 0o222
        os.link(p,B/p.name)
    rec['sources'].append(e)
for name in ['ForestNatWork','ForestNatSplit','ChildrenTrace','AffordableCalls','HighTrace','Rule4Trace']:
    p=D.parent/(name+'.lean');assert p.read_bytes()==(P/p.name).read_bytes()
    successful=[]
    for f in sorted(P.glob('live-compile-*/receipt.json')):
        c=json.loads(f.read_text())
        for run in c.get('runs',[]):
            if run['module']==name and run['exit']==0 and c.get('status')=='PASS_AUTHOR_LIVE_GUARDED_COMPILE':
                assert run['source_sha256']==sha(p)
                successful.append((f,run))
    assert successful,name
    f,run=successful[-1]
    for suffix in ['.lean','.olean']:
        src=P/(name+suffix);dst=B/src.name;shutil.copyfile(src,dst);dst.chmod(0o444)
    rec['own_completed'].append(dict(module=name,source_sha256=sha(p),olean_sha256=sha(B/(name+'.olean')),receipt=str(f.relative_to(R)),receipt_sha256=sha(f)))
shutil.copyfile(P/'lean-toolchain',B/'lean-toolchain')
rec['status']='PASS_EXACT_CHECKPOINT_CONTINUATION_SEED';save()
(D/'RESUME-BUILD-v1.json').write_text(json.dumps(dict(directory=str(B.relative_to(R)),seed_receipt_sha256=sha(B/'RESUME-SEED-RECEIPT.json')),indent=2)+'\n')
print(rec['status'],len(rec['sources']),len(rec['own_completed']))
