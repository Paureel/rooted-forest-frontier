# One-shot exact immutable source-root reuse for the actual DP cost consumer.
from pathlib import Path
import datetime,hashlib,json,os,shutil
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
M=D.parent/'ordinary_work_integration/HARD2-WORK-MANIFEST-v1.json';assert sha(M)=='337498c1f697edff18d0403616e62465e36a86192aeaba92916ef5643bd41932'
m=json.loads(M.read_text());P=R/m['canonical_build'];A=R/m['canonical_audit'];pins={e['path']:e['sha256'] for e in m['immutable_files']};assert sha(A/'certificate.json')==m['certificate_sha256']
c=json.loads((A/'certificate.json').read_text());assert c['status']=='PASS_AUTHOR_ACTUAL_HARD2_WORK_CONSUMER_SOURCE_PRODUCER'
assert shutil.disk_usage(R).free>=3*(1<<30)
B=R/'results'/('algorithm-universal233-allgood-local-work-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));B.mkdir();(B/'lean-toolchain').write_bytes((P/'lean-toolchain').read_bytes())
rec=dict(status='SOURCE_SEED_CHECKING',all_main_milestones='OPEN',independent_acceptance=False,seed_manifest=str(M.relative_to(R)),seed_manifest_sha256=sha(M),seed_audit=str(A.relative_to(R)),seed_audit_sha256=sha(A/'certificate.json'),sources=[])
def save():(B/'SEED-RECEIPT.json').write_text(json.dumps(rec,indent=2)+'\n')
save()
try:
 for e in c['sources']:
  n=e['module']
  for suffix,key in [('.lean','source_sha256'),('.olean','olean_sha256')]:
   p=P/(n+suffix);assert sha(p)==e[key]==pins[str(p.relative_to(R))];assert not p.stat().st_mode&0o222
   os.link(p,B/p.name)
  rec['sources'].append(e)
 rec['status']='PASS_EXACT_READONLY_SOURCE_SEED';save();print(rec['status'],len(rec['sources']),flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-BUILD-v1.json').write_text(json.dumps(dict(directory=str(B.relative_to(R)),seed_receipt_sha256=sha(B/'SEED-RECEIPT.json')),indent=2)+'\n')
