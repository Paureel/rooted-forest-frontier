#!/usr/bin/env python3
"""One-shot isolated author source/kernel/stored-producer replay.
The ghost is noncomputable proof support; no executable/runtime claim.
"""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,time
import audit
D=Path(__file__).resolve().parent;R=D.parents[4]
O=R/'results'/('algorithm-ordinary-dispatch-forest-min-completion-replay-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
def adapted_pin(src,h):
 if hashlib.sha256(src.encode()).hexdigest()!=h:raise ValueError('ADAPTED_BYTE_MISMATCH')
def clean(s):return re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',s,flags=re.S))
M=R/'research/rmaf/algorithm/universal233/forest_solver/FOREST-SOLVER-MANIFEST-v3.json'
pin(M,'89937a6f71bceb2dbeb64917b4b805e8f193fa485b00ec28acecdc95d047dcf5')
prior=json.loads(M.read_text())['immutable_files'];assert len(prior)==540
for e in prior:pin(R/e['path'],e['sha256'])
MF=D/'FOREST-MIN-COMPLETION-MANIFEST-v1.json'
if MF.exists():
 for e in json.loads(MF.read_text())['immutable_files']:pin(R/e['path'],e['sha256'])
entries=json.loads((D/'STACK-PINS.json').read_text());mods=[e['module'] for e in entries]
assert len(mods)==79 and len(mods)==len(set(mods))
rec=dict(status='RUNNING',claim_status='MATHEMATICAL_GHOST_COMPLETION_ONLY',source_entries=entries,runs=[],controls={},
 ghost_noncomputable=True,actual_callback_global_IH=False,executable_solver=False,runtime_claim=False,source_work_claim=False,
 global_milestones='ALL_OPEN',improved_base=0,novelty=False,independent_acceptance=False,
 independence='AUTHOR DEVELOPMENT. Completed GenericForest v3 and completed author detector contacts; no unfinished caller/classifier/reviewer code.',
 input_hashes={},scope_amendment_sha256=sha(R/'research/rmaf/algorithm/verification/ORIGIN-AUDIT-SCOPE-AMENDMENT-v1.md'),
 preserved_forest_v3=dict(manifest=str(M.relative_to(R)),sha256=sha(M),immutable_files_verified=len(prior)))
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
for e in entries:
 p=R/e['path'];pin(p,e['sha256']);src=p.read_text()
 for a,b in e.get('adaptations',{}).items():src=src.replace('import '+a+'\n','import '+b+'\n')
 adapted_pin(src,e['adapted_sha256'])
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(src)),e['path']
 if p.parent==D:assert not re.search(r'#(eval|reduce)\b',clean(src))
 (O/(e['module']+'.lean')).write_text(src)
core=(D/'ForestMinimumCompletion.lean').read_text()
assert 'noncomputable def minimumCallback' in core and 'noncomputable def ghost' in core
for p in D.iterdir():
 if p.is_file() and p.name not in {MF.name,'LATEST-REPLAY-v1.json'}:
  rec['input_hashes'][str(p.relative_to(R))]=sha(p)
  if p.suffix in {'.md','.json'} or p.name=='MinPreFalse.lean':(O/p.name).write_bytes(p.read_bytes())
C=R/'results/algorithm-universal233-forest-solver-20261015T114224630584Z'
(O/'lean-toolchain').write_bytes((C/'lean-toolchain').read_bytes());save()
for n in ['bootloops-lean','bootloops-lake']:
 p=subprocess.run([str(R/n),'--version'],cwd=O,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
 (O/(n+'-version.log')).write_text(p.stdout);assert p.returncode==0
rec['controls']['producer']=audit.detector_controls(O);save()
def run(n,build=False,want=0):
 start=time.monotonic();p=audit.run_lean(O,n,build)
 rec['runs'].append(dict(module=n,exit=p.returncode,seconds=time.monotonic()-start));save()
 assert p.returncode==want,(n,p.stdout[-8000:]);return p
(O/'MinStdTrue.lean').write_text('import Std\nexample : (2:Nat)+3=5 := by decide\n')
(O/'MinStdFalse.lean').write_text('import Std\nexample : (2:Nat)+3=6 := by decide\n')
run('MinStdTrue');p=run('MinStdFalse',want=1);assert p.stdout.count('is false')==1
for n in mods:run(n,True);print('BUILT',n,flush=True)
p=run('MinPreFalse',want=1);assert p.stdout.count('is false')==4;rec['controls']['false_math']=dict(rejected=4)
(O/'MinProducerAudit.lean').write_text(audit.audit_source(mods));p=run('MinProducerAudit');rows,ss,paths=audit.parse(p.stdout,mods,O)
keys=['LocalOrdinaryIH','nat_minimum_from_witness','minimum_from_original_AF','minimum_feasible_from_original_AF',
 'minimumCallback','minimumCallback_sound','minimumCallback_complete','minimumCallback_none_iff',
 'ghost','ghost_eq_actual','ghost_above_budget','ghost_global_ordinaryIH','ordinaryIH_extension']
for key in keys:assert any(r['name']=='ForestMinCompletion.'+key for r in rows),key
for tag,bad in [('missing_row',re.sub(r'^PRODUCERJSON\|.*\n','',p.stdout,count=1,flags=re.M)),
 ('duplicate_row',p.stdout+'PRODUCERJSON|'+json.dumps(rows[0])+'\n'),
 ('foreign_path',p.stdout.replace('PATH|RMAF|'+str(O/'RMAF.olean'),'PATH|RMAF|/tmp/foreign/RMAF.olean',1))]:
 try:audit.parse(bad,mods,O)
 except AssertionError:rec['controls'][tag]='CAUGHT'
 else:raise AssertionError('CORRUPTION_SURVIVED|'+tag)
for tag,fn in [('source_pin',lambda:pin(R/entries[0]['path'],'0'*64)),
 ('adapted_bytes',lambda:adapted_pin((O/(mods[0]+'.lean')).read_text()+' ',entries[0]['adapted_sha256']))]:
 try:fn()
 except ValueError:rec['controls'][tag]='CAUGHT'
 else:raise AssertionError('CORRUPTION_SURVIVED|'+tag)
(O/'MinInterfaces.lean').write_text('import MinimumCompletionControls\n'+''.join('#check ForestMinCompletion.'+k+'\n' for k in keys))
run('MinInterfaces')
for e in entries:pin(R/e['path'],e['sha256'])
for path,h in rec['input_hashes'].items():pin(R/path,h)
for e in prior:pin(R/e['path'],e['sha256'])
ax=sorted({a for r in rows for a in r['axiom_references']});assert set(ax)<=audit.ALLOW
rec.update(status='PASS_AUTHOR_KERNEL_PROOF_ONLY',source_builds=len(mods),stored_producer_occurrences=len(rows),axiom_union=ax,
 module_counts={m:int(n) for m,n in ss},interfaces=keys,
 skipped=['toolkit-wide suite','AF census','unfinished caller/schedule/disjoint congruence','fresh independent review','actual executable/runtime closure'],
 source_work='NO CLAIM. Noncomputable ghost is erased mathematical proof support; byte/producer pins are verification correspondences only.')
save();(O/'producer-occurrences.json').write_text(json.dumps(rows,indent=2)+'\n')
(O/'VERDICT.txt').write_text('PASS_AUTHOR_KERNEL_PROOF_ONLY\nDerived minimum and budget-local all-pair ghost extension compile; no executable/runtime closure.\n')
if not MF.exists():(D/'LATEST-REPLAY-v1.json').write_text(json.dumps(dict(receipt=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n')
print('PASS_AUTHOR_KERNEL_PROOF_ONLY',len(mods),'modules;',len(rows),'stored producer occurrences;',','.join(ax));print(O)
