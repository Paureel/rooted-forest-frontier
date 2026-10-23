#!/usr/bin/env python3
"""One-shot isolated Case322 source/kernel/producer-occurrence author replay.
All scientific work is author DEVELOPMENT; the complete local dispatch is OPEN.
"""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,time
import audit
D=Path(__file__).resolve().parent;R=D.parents[4]
O=R/'results'/('algorithm-universal233-rule5-case322-extraction-replay-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
def adapted_pin(src,h):
 if hashlib.sha256(src.encode()).hexdigest()!=h:raise ValueError('ADAPTED_BYTE_MISMATCH')
def clean(s):return re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',s,flags=re.S))
M=D.parent/'rule5_local/RULE5-LOCAL-MANIFEST-v1.json';pin(M,'411981d5b35caf6b79b576247baa99af4bd5ae2da8d1884c084a0dfb7a9d2386')
for e in json.loads(M.read_text())['immutable_files']:pin(R/e['path'],e['sha256'])
V1=D.parent/'rule5_case322/RULE5-CASE322-MANIFEST-v1.json';pin(V1,'2d5f9c672e7d2a2dc23e7a7c5434200ccd46bcb053188ff51c4954623d164763')
for e in json.loads(V1.read_text())['immutable_files']:pin(R/e['path'],e['sha256'])
MF=D/'RULE5-CASE322-EXTRACTION-MANIFEST-v1.json'
if MF.exists():
 for e in json.loads(MF.read_text())['immutable_files']:pin(R/e['path'],e['sha256'])
entries=json.loads((D/'STACK-PINS.json').read_text());mods=[e['module'] for e in entries];assert len(mods)==len(set(mods))
rec=dict(status='RUNNING',claim_status='OPEN_UNIVERSAL_CURRENT_GUARD',source_entries=entries,runs=[],controls={},
 complete_local_case322=False,global_milestones='ALL_OPEN',full_algorithm=False,improved_base=0,novelty=False,
 independence='AUTHOR DEVELOPMENT. Prior incidental contact remains in the frozen predecessor ledger; no independent credit.',
 input_hashes={},scope_amendment_sha256=sha(R/'research/rmaf/algorithm/verification/ORIGIN-AUDIT-SCOPE-AMENDMENT-v1.md'))
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
for e in entries:
 p=R/e['path'];pin(p,e['sha256']);src=p.read_text()
 for a,b in e.get('adaptations',{}).items():src=src.replace('import '+a+'\n','import '+b+'\n')
 adapted_pin(src,e['adapted_sha256']);assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(src)),e['path']
 (O/(e['module']+'.lean')).write_text(src)
for p in D.iterdir():
 if p.is_file() and p.name not in {'RULE5-CASE322-EXTRACTION-MANIFEST-v1.json','LATEST-REPLAY-v1.json'}:
  rec['input_hashes'][str(p.relative_to(R))]=sha(p)
  if p.suffix in {'.md','.json'} or p.name=='ExtractionFalse.lean':(O/p.name).write_bytes(p.read_bytes())
(O/'lean-toolchain').write_bytes((D.parent/'cherry_branching/lean-toolchain').read_bytes());save()
for n in ['bootloops-lean','bootloops-lake']:
 p=subprocess.run([str(R/n),'--version'],cwd=O,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
 (O/(n+'-version.log')).write_text(p.stdout);assert p.returncode==0
rec['controls']['producer']=audit.detector_controls(O);save()
def run(n,build=False,want=0):
 t=time.monotonic();p=audit.run_lean(O,n,build);rec['runs'].append(dict(module=n,exit=p.returncode,seconds=time.monotonic()-t));save()
 assert p.returncode==want,(n,p.stdout[-8000:]);return p
(O/'C322StdTrue.lean').write_text('import Std\nexample : (2:Nat)+3=5 := by decide\n')
(O/'C322StdFalse.lean').write_text('import Std\nexample : (2:Nat)+3=6 := by decide\n')
run('C322StdTrue');p=run('C322StdFalse',want=1);assert p.stdout.count('is false')==1
for n in mods:run(n,True);print('BUILT',n,flush=True)
p=run('ExtractionFalse',want=1);assert p.stdout.count('is false')==3;rec['controls']['false_math']=dict(rejected=3)
(O/'C322ProducerAudit.lean').write_text(audit.audit_source(mods));p=run('C322ProducerAudit');rows,ss,paths=audit.parse(p.stdout,mods,O)
for key in ['bottom_actual_pendants','oriented_split_saving','rawPlan_original_cover','rawPlan_conditional_minimum','operational_role_binding','bside_without_a_literal_spec','rawPlan_LIST_mass_bound']:
 assert any(r['name'].endswith('.'+key) for r in rows),key
for tag,bad in [('missing_row',re.sub(r'^PRODUCERJSON\|.*\n','',p.stdout,count=1,flags=re.M)),('duplicate_row',p.stdout+'PRODUCERJSON|'+json.dumps(rows[0])+'\n'),('foreign_path',p.stdout.replace('PATH|RMAF|'+str(O/'RMAF.olean'),'PATH|RMAF|/tmp/foreign/RMAF.olean',1))]:
 try:audit.parse(bad,mods,O)
 except AssertionError:rec['controls'][tag]='CAUGHT'
 else:raise AssertionError('CORRUPTION_SURVIVED|'+tag)
for tag,fn in [('source_pin',lambda:pin(R/entries[0]['path'],'0'*64)),('adapted_bytes',lambda:adapted_pin((O/(mods[0]+'.lean')).read_text()+' ',entries[0]['adapted_sha256']))]:
 try:fn()
 except ValueError:rec['controls'][tag]='CAUGHT'
 else:raise AssertionError('CORRUPTION_SURVIVED|'+tag)
keys=['bottom_actual_pendants','bottom_two_cut_orders','oriented_split_saving','oriented_easy_exchange','rawPlan_original_cover','rawPlan_conditional_minimum','operational_role_binding','guard_swap','callbacks_swap','bside_literal_spec','cside_literal_spec','bside_without_a_literal_spec','arcPartition_current_checks','target_currentGuard_of_nonredundant','rawPlan_cost_classes','rawPlan_callbacks_decrease','rawPlan_LIST_mass_bound']
(O/'C322Interfaces.lean').write_text('import PathSpecification\nimport ExtractionRootControls\n'+''.join('#check Universal233.Case322Extraction.'+k+'\n' for k in keys));run('C322Interfaces')
for e in entries:pin(R/e['path'],e['sha256'])
for path,h in rec['input_hashes'].items():pin(R/path,h)
ax=sorted({a for r in rows for a in r['axiom_references']});assert set(ax)<=audit.ALLOW
rec.update(status='PASS_AUTHOR_KERNEL_OPEN',source_builds=len(mods),stored_producer_occurrences=len(rows),axiom_union=ax,
 module_counts={m:int(n) for m,n in ss},interfaces=keys,
 skipped=['toolkit-wide suite','old colored census','finite AF census','fresh independent review','universal paid-current-guard proof','whole recursive solver'],
 source_work='Qualified inspection only; bit/payload correspondence and final recovery separate.')
save();(O/'producer-occurrences.json').write_text(json.dumps(rows,indent=2)+'\n');(O/'VERDICT.txt').write_text('PASS_AUTHOR_KERNEL_OPEN\nComputed original-path plan AF cover and source orientations compile; universal paid current guard remains OPEN.\n')
if not MF.exists():(D/'LATEST-REPLAY-v1.json').write_text(json.dumps(dict(receipt=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n')
print('PASS_AUTHOR_KERNEL_OPEN',len(mods),'modules;',len(rows),'stored producer occurrences;',','.join(ax));print(O)
