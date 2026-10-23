#!/usr/bin/env python3
"""One-shot byte-preserving release of completed interrupted-task inputs.
Existing final_classification freeze helper would mutate prior paths; this
wrapper snapshots and freezes only the newly owned release path instead.
"""
from pathlib import Path
import datetime,hashlib,json,shutil,time
D=Path(__file__).resolve().parent;R=D.parents[4]
def digest(b):return hashlib.sha256(b).hexdigest()
def exact(b,h):
 if digest(b)!=h:raise ValueError('HASH_MISMATCH')
def state(r):
 if r.get('status')!='PASS_AUTHOR_KERNEL_OPEN':raise ValueError('INCOMPLETE_RECEIPT')
H='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
exact(b'abc',H)
controls={'clean_hash':'PASS'}
for tag,b,h in [('changed_bytes',b'abd',H),('changed_hash',b'abc','0'*64)]:
 try:exact(b,h)
 except ValueError:controls[tag]='CAUGHT'
 else:raise AssertionError(tag)
state({'status':'PASS_AUTHOR_KERNEL_OPEN'});controls['clean_status']='PASS'
try:state({'status':'RUNNING_AUTHOR'})
except ValueError:controls['incomplete_status']='CAUGHT'
else:raise AssertionError('incomplete_status')
S=D.parent/'rule5_final_classification'
latest=json.loads((S/'LATEST-REPLAY-v1.json').read_text());O=R/latest['receipt']
exact((O/'certificate.json').read_bytes(),latest['certificate_sha256'])
cert=json.loads((O/'certificate.json').read_text());state(cert)
for p,h in cert['input_hashes'].items():exact((R/p).read_bytes(),h)
entries=cert['source_entries']
for e in entries:exact((R/e['path']).read_bytes(),e['sha256'])
assert cert['source_builds']==len(entries)>0
assert cert['stored_producer_occurrences']>0
assert set(cert['axiom_union'])<={'propext','Classical.choice','Quot.sound'}
for old in [D.parent/'rule5_classification/CLASSIFICATION-MANIFEST-v1.json',D.parent/'rule5_local/RULE5-LOCAL-MANIFEST-v1.json']:
 for e in json.loads(old.read_text())['immutable_files']:exact((R/e['path']).read_bytes(),e['sha256'])
F=D/'structural-input-release-v1'
if F.exists():raise SystemExit('NEW_RELEASE_ALREADY_EXISTS_NO_OVERWRITE')
F.mkdir()
files={p for p in S.iterdir() if p.is_file()}
files|={p for p in O.rglob('*') if p.is_file()}
files|={R/e['path'] for e in entries}
for n in ['CONTROLS-PIN-v1.md','preserve_structural.py']:files.add(D/n)
rows=[]
for p in sorted(files):
 b=p.read_bytes();q=F/p.relative_to(R);q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
 exact(q.read_bytes(),digest(b));q.chmod(0o444)
 rows.append({'original':str(p.relative_to(R)),'snapshot':str(q.relative_to(R)),'sha256':digest(b),'bytes':len(b)})
rec={'status':'FROZEN_AUTHOR_STRUCTURAL_INPUT_COPY_OPEN','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
'controls':controls,'original_receipt':latest,'source_builds':cert['source_builds'],
'stored_producer_occurrences':cert['stored_producer_occurrences'],'axiom_union':cert['axiom_union'],
'original_paths_untouched':True,'independent_credit':0,'main_milestones':'ALL_OPEN','immutable_files':rows}
M=F/'MANIFEST.json';M.write_text(json.dumps(rec,indent=2)+'\n');M.chmod(0o444)
(D/'STRUCTURAL-INPUT-RELEASE-v1.json').write_text(json.dumps({'manifest':str(M.relative_to(R)),'sha256':digest(M.read_bytes())},indent=2)+'\n')
print(rec['status'],len(rows),'files;',rec['source_builds'],'modules;',rec['stored_producer_occurrences'],'producer occurrences')
