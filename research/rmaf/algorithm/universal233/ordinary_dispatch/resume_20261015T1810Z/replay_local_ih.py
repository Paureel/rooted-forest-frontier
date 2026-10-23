#!/usr/bin/env python3
"""One-shot source-bound author seal of saved executable-locality transfer.
Reuses completed author detector, so it is not an independent verification.
"""
from pathlib import Path
import datetime, hashlib, importlib.util, json, os, re, subprocess, time
D=Path(__file__).resolve().parent;R=D.parents[5]
P=D.parent/'forest_local_ih';M=R/'research/rmaf/algorithm/ordinary_dispatch/forest_min_completion'
O=R/'results'/('algorithm-universal233-forest-local-ih-replay-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
sp=importlib.util.spec_from_file_location('localih_completed_detector',M/'audit.py');A=importlib.util.module_from_spec(sp);sp.loader.exec_module(A)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(data,expected):assert hashlib.sha256(data).hexdigest()==expected,'SOURCE_OR_ADAPTED_PIN_MISMATCH'
entries=json.loads((M/'STACK-PINS.json').read_text())
for name in ['LocalCongruence','LocalExact','LocalControls','TransferControls']:
 p=P/(name+'.lean');entries.append(dict(module=name,path=str(p.relative_to(R)),sha256=sha(p),adaptations={},adapted_sha256=sha(p)))
mods=[x['module'] for x in entries];assert len(mods)==83 and len(set(mods))==83
rec=dict(status='FRESH_CONTROLS_RUNNING',scope='AUTHOR bounded-local-IH exactness transfer for unchanged executable GenericForest.solve',all_main_milestones='OPEN',independent_acceptance=False,full_ordinary_solver=False,runtime_claim=False,source_work_claim=False,ghost_in_executable=False,source_entries=entries,runs=[],controls={},inputs={})
for p in [Path(__file__),D/'AUDIT-PLAN-v1.md',M/'audit.py',M/'FOREST-MIN-COMPLETION-MANIFEST-v1.json',M/'STACK-PINS.json',P/'PRECONSTRUCTION-RECEIPT-v1.json',P/'TRANSFER-CONTROLS-dev1.json']:
 rec['inputs'][str(p.relative_to(R))]=sha(p)
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
def run(name,build=False,want=0):
 start=time.monotonic();p=A.run_lean(O,name,build);rec['runs'].append(dict(module=name,exit=p.returncode,seconds=time.monotonic()-start));save();assert p.returncode==want,(name,p.stdout[-7000:]);return p
save();(O/'lean-toolchain').write_bytes((R/'research/rmaf/lean/lean-toolchain').read_bytes())
try:
 # Full fresh completed producer detector controls before scientific rebuild.
 rec['controls']['producer']=A.detector_controls(O)
 empty='e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'
 pin(b'',empty)
 try:pin(b'x',empty)
 except AssertionError:rec['controls']['source_and_adapted_pin_corruption']='CAUGHT_BY_PRODUCTION_PIN'
 else:raise AssertionError('CORRUPTION_SURVIVED')
 (O/'StdTrue.lean').write_text('import Std\nexample : (2:Nat)+3=5 := by decide\n');run('StdTrue')
 (O/'StdFalse.lean').write_text('import Std\nexample : (2:Nat)+3=6 := by decide\n');run('StdFalse',want=1)
 frozen=json.loads((M/'FOREST-MIN-COMPLETION-MANIFEST-v1.json').read_text());assert sha(M/'FOREST-MIN-COMPLETION-MANIFEST-v1.json')=='0be74cd7bfc28cfaa382ea0610472bea7d64e601a7cab5919727ee993ca2cef4'
 for e in frozen['immutable_files']:pin((R/e['path']).read_bytes(),e['sha256'])
 rec['frozen_completion_members_verified']=len(frozen['immutable_files'])
 for e in entries:
  src=R/e['path'];pin(src.read_bytes(),e['sha256']);s=src.read_text()
  for a,b in e['adaptations'].items():s=s.replace('import '+a+'\n','import '+b+'\n')
  pin(s.encode(),e['adapted_sha256'])
  clean=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',s,flags=re.S))
  assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean),e['path']
  (O/(e['module']+'.lean')).write_text(s)
 rec['status']='ISOLATED_SOURCE_REPLAY_RUNNING';save()
 for n in mods:run(n,True);print('BUILT',n,flush=True)
 for n in ['FalseDiscount','FalseUnboundedTransfer']:
  (O/(n+'.lean')).write_bytes((P/(n+'.lean')).read_bytes());run(n,want=1)
 rec['controls']['false_transfer_claims_rejected']=2
 (O/'LocalIHProducerAudit.lean').write_text(A.audit_source(mods));p=run('LocalIHProducerAudit');rows,ss,pp=A.parse(p.stdout,mods,O)
 for label,bad in [('missing_row',re.sub(r'^PRODUCERJSON\|.*\n','',p.stdout,count=1,flags=re.M)),('duplicate_row',p.stdout+'PRODUCERJSON|'+json.dumps(rows[0])+'\n'),('foreign_module_path',p.stdout.replace('PATH|RMAF|'+str(O/'RMAF.olean'),'PATH|RMAF|/tmp/foreign/RMAF.olean',1))]:
  try:A.parse(bad,mods,O)
  except AssertionError:rec['controls'][label]='CAUGHT'
  else:raise AssertionError('CORRUPTION_SURVIVED|'+label)
 keys=['GenericForest.LocalIH.run_congr','GenericForest.LocalIH.schedule_congr','GenericForest.LocalIH.disjointSolve_congr','GenericForest.LocalIH.solve_congr_budget','GenericForest.LocalIH.exact_at_budget_bound','GenericForest.LocalIH.exact_at_current_budget']
 for n in keys:assert any(r['name']==n for r in rows),n
 (O/'LocalIHInterfaces.lean').write_text('import TransferControls\n'+''.join('#check '+n+'\n' for n in keys));run('LocalIHInterfaces')
 for e in entries:pin((R/e['path']).read_bytes(),e['sha256'])
 for p,h in rec['inputs'].items():pin((R/p).read_bytes(),h)
 for e in frozen['immutable_files']:pin((R/e['path']).read_bytes(),e['sha256'])
 axs=sorted({a for r in rows for a in r['axiom_references']});assert set(axs)<=A.ALLOW
 rec.update(status='PASS_AUTHOR_LOCAL_IH_TRANSFER',source_builds=len(mods),stored_producer_occurrences=len(rows),axiom_union=axs,interfaces=keys,proof_ghost_scope='ForestMinimumCompletion occurs only as noncomputable erased theorem support. Actual program equality consumes all callbacks at b<=q, without properness or correctness premises. No runtime ghost/minimum oracle.',first_external_gap='Well-founded actual ordinary dispatcher must establish LocalOrdinaryIH for each actual callback and enforce selector/guard/child source contracts; complete source/bit/payload recurrence remains open.')
 save();(O/'VERDICT.txt').write_text('PASS_AUTHOR_LOCAL_IH_TRANSFER\nUnchanged forest execution is exact under budget-local ordinary IH. Full ordinary solver/runtime/base/novelty remain OPEN.\n');print(rec['status'],len(rows),'stored occurrences',flush=True)
except BaseException as e:
 rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-LOCAL-IH-v1.json').write_text(json.dumps(dict(directory=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n')
