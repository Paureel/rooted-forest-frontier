from pathlib import Path
import hashlib,json,stat
D=Path(__file__).resolve().parent;R=D.parents[5];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
t=R/'research/rmaf/monitoring/continuation-next-20261016T112422Z/RECOVERY-ATTEMPT-TARGET-v1.json';assert sha(t)=='21213642753eed5a10689af37d1005f5d0329b4cea152f5bae5157314d512be9'
target=json.loads(t.read_text());prior=R/target['previous_completed']['manifest'];assert sha(prior)==target['previous_completed']['sha256'];m=json.loads(prior.read_text());records={}
def record(p):
 s=p.stat();records[str(p.relative_to(R))]={'path':str(p.relative_to(R)),'sha256':sha(p),'mode':oct(stat.S_IMODE(s.st_mode)),'inode':s.st_ino,'device':s.st_dev}
for e in m['original_files']:
 p=R/e['path'];s=p.stat();assert sha(p)==e['sha256'] and oct(stat.S_IMODE(s.st_mode))==e['mode'] and s.st_ino==e['inode'] and s.st_dev==e['device'];record(p)
for e in m['immutable_files']:
 p=R/e['path'];assert sha(p)==e['sha256'] and not p.stat().st_mode&0o222;record(p)
for e in target['allowed_packages'].values():
 p=R/e['manifest'];assert sha(p)==e['sha256'];record(p)
record(t);record(prior)
(D/'DEPENDENCIES-BEFORE-v1.json').write_text(json.dumps({'members':list(records.values()),'previous_immutable_matched':len(m['immutable_files']),'previous_originals_matched':len(m['original_files'])},indent=2)+'\n')
(D/'TARGET-PINS-v1.json').write_text(json.dumps({'path':str(t.relative_to(R)),'sha256':sha(t),'allowed_packages':target['allowed_packages']},indent=2)+'\n')
print('PINNED',len(records),len(m['immutable_files']))
