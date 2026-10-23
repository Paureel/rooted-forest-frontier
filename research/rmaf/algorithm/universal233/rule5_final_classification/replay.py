#!/usr/bin/env python3
"""Fresh isolated author source replay; complete ordinary Rule5 stays OPEN."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,time
import audit
D=Path(__file__).resolve().parent;R=D.parents[4];V=D.parent/'rule5_classification';L=D.parent/'rule5_local'
M=D/'FINAL-CLASSIFICATION-MANIFEST-v1.json'
O=R/'results'/('algorithm-universal233-rule5-final-classification-replay-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
def adapted_pin(s,h):
 if hashlib.sha256(s.encode()).hexdigest()!=h:raise ValueError('ADAPTED_BYTE_MISMATCH')
def clean(s):return re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',s,flags=re.S))
old=V/'CLASSIFICATION-MANIFEST-v1.json';pin(old,'0bcb3ff2675f9bd9a49072029b4163d8587325678b102b76c7acf597e46e7551')
older=L/'RULE5-LOCAL-MANIFEST-v1.json';pin(older,'411981d5b35caf6b79b576247baa99af4bd5ae2da8d1884c084a0dfb7a9d2386')
old_entries=json.loads(old.read_text())['immutable_files']+json.loads(older.read_text())['immutable_files']
old_modes={e['path']:(R/e['path']).stat().st_mode for e in old_entries}
for e in old_entries:pin(R/e['path'],e['sha256'])
if M.exists():
 for e in json.loads(M.read_text())['immutable_files']:pin(R/e['path'],e['sha256'])
allowed={e['path']:e['sha256'] for e in json.loads((V/'STACK-PINS.json').read_text())}
pre=json.loads((D/'PREPROOF-RECEIPT-v1.json').read_text());pin(R/pre['receipt']/'certificate.json',pre['sha256'])
pc=json.loads((R/pre['receipt']/'certificate.json').read_text());assert pc['status']=='PASS_FINITE_DEVELOPMENT_CONTROLS'
for p,h in pc['input_pins'].items():pin(R/p,h)
entries=json.loads((D/'STACK-PINS.json').read_text());mods=[e['module'] for e in entries]
assert len(mods)==len(set(mods))
record=dict(status='RUNNING_AUTHOR',complete_local_rule5=False,full_algorithm=False,smaller_base=False,novelty=False,
 main_milestones='ALL_OPEN',fresh_independent_acceptance=False,old_manifest_sha256=sha(old),preproof=pre,
 source_entries=entries,runs=[],controls={},input_hashes={},
 scope_amendment_sha256=sha(R/'research/rmaf/algorithm/verification/ORIGIN-AUDIT-SCOPE-AMENDMENT-v1.md'))
def save():(O/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
for e in entries:
 p=R/e['path'];pin(p,e['sha256'])
 if not p.is_relative_to(D):assert allowed.get(e['path'])==e['sha256'],'UNPINNED_DEVELOPMENT_CONTACT'
 src=p.read_text()
 for a,b in e.get('adaptations',{}).items():src=src.replace('import '+a+'\n','import '+b+'\n')
 adapted_pin(src,e['adapted_sha256'])
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(src)),e['path']
 (O/(e['module']+'.lean')).write_text(src)
for p in D.iterdir():
 if p.is_file() and p.name not in {'FINAL-CLASSIFICATION-MANIFEST-v1.json','LATEST-REPLAY-v1.json'}:
  record['input_hashes'][str(p.relative_to(R))]=sha(p)
  if p.suffix in {'.md','.json'} or p.name=='FinalFalseControls.lean':(O/p.name).write_bytes(p.read_bytes())
for n in ['Rule5FalsePreControls','Rule5FalseGraphControls']:(O/(n+'.lean')).write_bytes((L/(n+'.lean')).read_bytes())
(O/'ClassificationFalseControls.lean').write_bytes((V/'ClassificationFalseControls.lean').read_bytes())
(O/'lean-toolchain').write_bytes((D.parent/'cherry_branching/lean-toolchain').read_bytes());save()
def run(n,build=False,want=0):
 start=time.monotonic();p=audit.run_lean(O,n,build)
 record['runs'].append(dict(module=n,exit=p.returncode,seconds=time.monotonic()-start));save()
 assert p.returncode==want,(n,p.stdout[-9000:]);return p
for n in ['bootloops-lean','bootloops-lake']:
 p=subprocess.run([str(R/n),'--version'],cwd=O,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
 (O/(n+'-version.log')).write_text(p.stdout);assert p.returncode==0
producer=json.loads((D/'PRODUCER-PREFLIGHT-v1.json').read_text());P=R/producer['receipt'];pin(P/'manifest.json',producer['sha256'])
pcp=json.loads((P/'manifest.json').read_text());assert pcp['status']=='PASS_AUTHOR_STD_ONLY_PRODUCER_PREFLIGHT'
pin(D/'audit.py',pcp['instrument_sha256'])
for e in pcp['immutable_files']:pin(R/e['path'],e['sha256']);assert not ((R/e['path']).stat().st_mode & 0o222)
record['controls']['producer']=dict(frozen_receipt=producer,controls=pcp['controls']);save()
(O/'StdTrue.lean').write_text('import Std\nexample : (3:Nat)+4=7 := by decide\n')
(O/'StdFalse.lean').write_text('import Std\nexample : (3:Nat)+4=8 := by decide\n')
run('StdTrue');p=run('StdFalse',want=1);assert p.stdout.count('is false')==1
for n in mods:
 run(n,True);print('BUILT',n,flush=True)
for n,count in [('Rule5FalsePreControls',4),('Rule5FalseGraphControls',2),('ClassificationFalseControls',8),('FinalFalseControls',8)]:
 p=run(n,want=1);assert p.stdout.count('is false')==count
 record['controls'][n]=dict(rejected=count)
(O/'ProducerAudit.lean').write_text(audit.audit_source(mods));p=run('ProducerAudit')
rows,summaries,paths=audit.parse(p.stdout,mods,O)
required=['Universal233.Rule5FinalClassification.'+k for k in ['remaining_source_status','remaining_source_core','source_two_pendant_spine','remaining_full_source_geometry','incident_at_most_two','incident_one_or_two','actual_two_boundary_trichotomy','third_attachment_actual_root','selectBad_complete','boundary_selector_complete','remaining_classifier_complete','selected_source_geometry','final_classification_complete','final_selected_sound','final_prefix_child_solver','final_one_emits','final_third_root']]
for key in required:assert any(r['name']==key for r in rows),key
for tag,bad in [('missing_occurrence',re.sub(r'^PRODUCERJSON\|.*\n','',p.stdout,count=1,flags=re.M)),
 ('duplicate_occurrence',p.stdout+'PRODUCERJSON|'+json.dumps(rows[0])+'\n'),
 ('foreign_path',p.stdout.replace('PATH|RMAF|'+str(O/'RMAF.olean'),'PATH|RMAF|/tmp/foreign/RMAF.olean',1))]:
 try:audit.parse(bad,mods,O)
 except AssertionError:record['controls'][tag]='CAUGHT'
 else:raise AssertionError('CORRUPTION_SURVIVED|'+tag)
try:pin(R/entries[0]['path'],'0'*64)
except ValueError:record['controls']['source_pin']='CAUGHT'
else:raise AssertionError('SOURCE_PIN_CORRUPTION_SURVIVED')
try:adapted_pin((O/(mods[0]+'.lean')).read_text()+' ',entries[0]['adapted_sha256'])
except ValueError:record['controls']['adapted_bytes']='CAUGHT'
else:raise AssertionError('ADAPTED_BYTE_CORRUPTION_SURVIVED')
(O/'Interfaces.lean').write_text('import FinalControls\n'+''.join('#check '+k+'\n' for k in required))
run('Interfaces')
for e in entries:pin(R/e['path'],e['sha256'])
for p,h in record['input_hashes'].items():pin(R/p,h)
for e in old_entries:pin(R/e['path'],e['sha256']);assert (R/e['path']).stat().st_mode==old_modes[e['path']],('OLD_MODE_CHANGED',e['path'])
axs=sorted({a for r in rows for a in r['axiom_references']});assert set(axs)<=audit.ALLOW
record.update(status='PASS_AUTHOR_KERNEL_OPEN',source_builds=len(mods),stored_producer_occurrences=len(rows),
 axiom_union=axs,module_counts={m:int(n) for m,n in summaries},interfaces=required,
 completed_author_scope=['actual remaining source statuses','all source fork and root-context orientations','actual one/two target incident arcs','actual three attachment alternatives and root-c fork','exhaustive finite classifier and literal selected-source geometry','actual common-split witness emitter','preserved child-specific bounded prefix consumers'],
 structural_classifier_complete=True,first_gap='FIRST-GAP-v1.md: general-orientation remaining exchange and exact recursive consumers',
 skipped=['No toolkit-wide suite retry','No old large census','No unfinished Figure15.2/common-split/reviewer source contact','No fresh independent review','No full algorithm/base/novelty claim'])
save();(O/'producer-occurrences.json').write_text(json.dumps(rows,indent=2)+'\n')
(O/'VERDICT.txt').write_text('PASS_AUTHOR_KERNEL_OPEN\nRemaining structural classifier compiles; complete ordinary Rule5 recursive consumers remain OPEN.\n')
if not M.exists():(D/'LATEST-REPLAY-v1.json').write_text(json.dumps(dict(receipt=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n')
print('PASS_AUTHOR_KERNEL_OPEN',len(mods),'source modules;',len(rows),'stored producer occurrences;',','.join(axs));print(O)
