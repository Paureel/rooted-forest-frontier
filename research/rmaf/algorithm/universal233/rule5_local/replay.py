#!/usr/bin/env python3
"""One-shot isolated OPEN Rule5 author replay, with producer occurrence audit."""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,time
import audit
D=Path(__file__).resolve().parent;R=D.parents[4]
O=R/'results'/('algorithm-universal233-rule5-local-replay-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
def clean(s):return re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',s,flags=re.S))
def adapted_pin(src,h):
 if hashlib.sha256(src.encode()).hexdigest()!=h:raise ValueError('ADAPTED_BYTE_MISMATCH')
M=D/'RULE5-LOCAL-MANIFEST-v1.json'
if M.exists():
 for e in json.loads(M.read_text())['immutable_files']:pin(R/e['path'],e['sha256'])
parentM=D.parent/'cherry_branching/CHERRY-BRANCH-MANIFEST-v1.json'
pin(parentM,'5ffb1fa6e9810485f60ced7e4e5d9cccc0f915fa95e9ba9e4998550b17eebe5d')
frozen={}
for e in json.loads(parentM.read_text())['immutable_files']:pin(R/e['path'],e['sha256']);frozen[e['path']]=e['sha256']
# The frozen completed DEV-STACK is the exact source-import pin ledger. Some
# original sources live in earlier completed packages, rather than being direct
# rows of the cherry package's immutable local/source-copy manifest.
for e in json.loads((D.parent/'cherry_branching/DEV-STACK.json').read_text()):
 frozen[e['path']]=e['sha256']
pre=json.loads((D/'PREPROOF-RECEIPT-v1.json').read_text());pin(R/pre['receipt']/'certificate.json',pre['sha256'])
preCert=json.loads((R/pre['receipt']/'certificate.json').read_text())
for p,h in preCert['pins'].items():pin(R/p,h)
assert preCert['status']=='PASS_PREPROOF_DEVELOPMENT'
entries=json.loads((D/'STACK-PINS.json').read_text());mods=[e['module'] for e in entries]
assert len(mods)==len(set(mods))
record=dict(status='RUNNING_OPEN_AUTHOR',claim_status='OPEN_FIRST_GRAPH_CLASSIFICATION_GAP',main_milestones='ALL_OPEN',
 fresh_independent_acceptance=False,complete_local_rule5=False,full_algorithm=False,smaller_base=False,novelty=False,
 preproof=pre,source_entries=entries,runs=[],controls={},input_hashes={},scope_amendment_sha256=sha(R/'research/rmaf/algorithm/verification/ORIGIN-AUDIT-SCOPE-AMENDMENT-v1.md'))
def save():(O/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
for e in entries:
 p=R/e['path'];pin(p,e['sha256'])
 if not p.is_relative_to(D):assert frozen.get(e['path'])==e['sha256'],'UNFROZEN_DEVELOPMENT_CONTACT|'+e['path']
 src=p.read_text()
 for a,b in e.get('adaptations',{}).items():src=src.replace('import '+a+'\n','import '+b+'\n')
 adapted_pin(src,e['adapted_sha256'])
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(src)),e['path']
 (O/(e['module']+'.lean')).write_text(src)
for p in D.glob('*'):
 if p.is_file() and p.name not in {'RULE5-LOCAL-MANIFEST-v1.json','LATEST-REPLAY-v1.json'}:
  # LATEST is this run's derived output pointer, not an input. After freeze
  # it is immutable with the manifest and the replay no longer updates it.
  record['input_hashes'][str(p.relative_to(R))]=sha(p)
  if p.suffix in {'.md','.json'} or p.name.startswith('Rule5False'):(O/p.name).write_bytes(p.read_bytes())
(O/'lean-toolchain').write_bytes((D.parent/'cherry_branching/lean-toolchain').read_bytes());save()
def run(n,build=False,want=0):
 start=time.monotonic();p=audit.run_lean(O,n,build)
 record['runs'].append(dict(module=n,exit=p.returncode,seconds=time.monotonic()-start));save()
 assert p.returncode==want,(n,p.stdout[-8000:]);return p
for n in ['bootloops-lean','bootloops-lake']:
 p=subprocess.run([str(R/n),'--version'],cwd=O,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
 (O/(n+'-version.log')).write_text(p.stdout);assert p.returncode==0
# Fresh Std-only clean/coalesced/hostile controls precede candidate audit.
record['controls']['producer']=audit.detector_controls(O);save()
(O/'StdTrue.lean').write_text('import Std\nexample : (2:Nat)+3=5 := by decide\n')
(O/'StdFalse.lean').write_text('import Std\nexample : (2:Nat)+3=6 := by decide\n')
run('StdTrue');p=run('StdFalse',want=1);assert p.stdout.count('is false')==1
for n in mods:
 run(n,True)
 print('BUILT',n,flush=True)
for n,count in [('Rule5FalsePreControls',4),('Rule5FalseGraphControls',2)]:
 p=run(n,want=1);assert p.stdout.count('is false')==count
 record['controls'][n]=dict(rejected=count)
(O/'ProducerAudit.lean').write_text(audit.audit_source(mods));p=run('ProducerAudit')
rows,ss,paths=audit.parse(p.stdout,mods,O)
assert any(r['producer']=='Rule5Graph' and r['name'].endswith('commonSplit_emits') for r in rows)
assert any(r['producer']=='Rule5Case321' and r['name'].endswith('actual_case321_exchange') for r in rows)
assert any(r['producer']=='Rule5Case323' and r['name'].endswith('actual_case323_exchange') for r in rows)
for tag,bad in [('missing_row',re.sub(r'^PRODUCERJSON\|.*\n','',p.stdout,count=1,flags=re.M)),
                ('duplicate_row',p.stdout+'PRODUCERJSON|'+json.dumps(rows[0])+'\n')]:
 try:audit.parse(bad,mods,O)
 except AssertionError:record['controls'][tag]='CAUGHT'
 else:raise AssertionError('CORRUPTION_SURVIVED|'+tag)
for tag,bad in [('foreign_path',p.stdout.replace('PATH|RMAF|'+str(O/'RMAF.olean'),'PATH|RMAF|/tmp/foreign/RMAF.olean',1))]:
 try:audit.parse(bad,mods,O)
 except AssertionError:record['controls'][tag]='CAUGHT'
 else:raise AssertionError('CORRUPTION_SURVIVED|'+tag)
try:pin(R/entries[0]['path'],'0'*64)
except ValueError:record['controls']['source_pin']='CAUGHT'
else:raise AssertionError('SOURCE_PIN_CORRUPTION_SURVIVED')
try:adapted_pin((O/(mods[0]+'.lean')).read_text()+' ',entries[0]['adapted_sha256'])
except ValueError:record['controls']['adapted_bytes']='CAUGHT'
else:raise AssertionError('ADAPTED_BYTE_CORRUPTION_SURVIVED')
keys=['actual_one_incident_split','commonSplit_emits','original_crossing_clusters_exclude_block','figure153_block_exclusion',
 'splitTwo_original','splitTwo_refines','actual_hard2_exchange_from_split_saving','actual_hard2_exchange_from_split_saving_b',
 'case321_split_saving','actual_case321_exchange','case323_split_saving','actual_case323_exchange']
(O/'Interfaces.lean').write_text('import Rule5GraphControls\n'+''.join('#check Universal233.Rule5Local.'+k+'\n' for k in keys))
run('Interfaces')
for e in entries:pin(R/e['path'],e['sha256'])
for p,h in record['input_hashes'].items():pin(R/p,h)
ax=sorted({a for row in rows for a in row['axiom_references']});assert set(ax)<=audit.ALLOW
record.update(status='PASS_AUTHOR_KERNEL_OPEN',source_builds=len(mods),stored_producer_occurrences=len(rows),
 axiom_union=ax,module_counts={m:int(n) for m,n in ss},interfaces=keys,
 skipped=['No toolkit-wide suite retry','No independent reviewer','No old large census','No complete local selector cover','No global recursive solver'],
 qualified_source_work='SOURCE-WORK-v1.md inspection only')
save();(O/'producer-occurrences.json').write_text(json.dumps(rows,indent=2)+'\n')
(O/'VERDICT.txt').write_text('PASS_AUTHOR_KERNEL_OPEN\nActual graph prefix and two displayed-orientation exchanges compile; complete ordinary Rule5 remains OPEN.\n')
(D/'LATEST-REPLAY-v1.json').write_text(json.dumps(dict(receipt=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n') if not M.exists() else None
print('PASS_AUTHOR_KERNEL_OPEN',len(mods),'source modules;',len(rows),'stored producer occurrences;',','.join(ax));print(O)
