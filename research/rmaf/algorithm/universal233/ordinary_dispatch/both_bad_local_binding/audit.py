#!/usr/bin/env python3
"""New-module-only bounded audit using the exact frozen producer extractor."""
from pathlib import Path
import datetime,hashlib,json,shutil,sys
sys.dont_write_bytecode=True
import instrument,pilot
D=Path(__file__).resolve().parent;R=pilot.R;O=pilot.O
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
spec=json.loads((D/'ROOT-v2.json').read_text());freeze=json.loads((D/'POOL-FREEZE-CONFIRM-v1.json').read_text())
mods=['BindingPrecontrols','CallbackLocality','OrdinaryLocal','BothBadBinding','BindingControls']
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
def deps():
 pin(R/freeze['manifest']['path'],freeze['manifest']['sha256'])
 for e in spec['dependencies']:
  for f in e['files']:
   for k in ['pool_source','copied']:
    p=R/f[k];pin(p,f['sha256']);assert not p.stat().st_mode&0o222,'MUTABLE_DEPENDENCY'
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ');C=O/('certificate-'+stamp+'.json');F=O/('producer-records-'+stamp);F.mkdir();(O/('audit-'+stamp+'.source.py')).write_bytes((D/'audit.py').read_bytes())
rec={'status':'RUNNING_AUTHOR_BOTH_BAD_LOCAL_AUDIT','independent_credit':0,'main_milestones':'ALL_OPEN','root':str(O.relative_to(R)),
 'new_modules':[],'dependency_modules':len(spec['dependencies']),'root_pin_sha256':sha(D/'ROOT-v2.json'),'pool_freeze_confirmation_sha256':sha(D/'POOL-FREEZE-CONFIRM-v1.json'),
 'producer_preflight':spec['producer_preflight'],'instrument_sha256':sha(D/'instrument.py'),'runs':[],'input_hashes':{},
 'module_timeout_seconds':30,'live_disk_floor_bytes':3*1024**3,'producer_uncompressed_cap_bytes':8388608,'compressed_total_cap_bytes':256*1024**2,
 'audit_scope':'Five new stored producers only; full nonproof/opaque bodies retained. Theorem proof TEXT omitted only with actual ConstantInfo.getUsedConstantsAsSet references/full AX closure. All 169 imported source/olean pairs checked against the frozen fast pool; no dependency rebuilt.'}
def save():C.write_text(json.dumps(rec,indent=2)+'\n')
def run(n,want=0):
 before=set(O.glob(n+'-*.run.json'));s=pilot.run(n,want=want);p=next(iter(set(O.glob(n+'-*.run.json'))-before));rec['runs'].append({'path':str(p.relative_to(R)),'sha256':sha(p)});save();return s
save()
try:
 pin(D/'instrument.py',spec['instrument_sha256']);pre=spec['producer_preflight'];P=R/pre['manifest'];pin(P,pre['sha256']);pc=json.loads(P.read_text());pin(D/'instrument.py',pc['instrument_sha256'])
 for e in pc['immutable_files']:pin(R/e['path'],e['sha256'])
 pin(R/spec['overlap_manifest']['path'],spec['overlap_manifest']['sha256'])
 for n in ['RMAF','LocalExact']:
  try:pilot.run(n)
  except RuntimeError as e:assert str(e)=='REFUSE_LINKED_DEPENDENCY_COMPILATION|'+n
  else:raise AssertionError('DEPENDENCY_COMPILE_GUARD_FAILED')
 assert hashlib.sha256(b'abc').hexdigest()=='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
 assert hashlib.sha256(b'abc').hexdigest()!=hashlib.sha256(b'abd').hexdigest()
 deps()
 if shutil.disk_usage(D).free<3*1024**3:raise RuntimeError('DISK_FLOOR_3_GIB')
 for n in mods:
  p=D/(n+'.lean');pin(O/p.name,sha(p));assert (O/(n+'.olean')).exists()
  ok=[q for q in O.glob(n+'-*.run.json') if (lambda x:x['exit']==0 and not x['failure'] and x['source_sha256']==sha(p))(json.loads(q.read_text()))];assert ok,'MISSING_EXACT_BUILD|'+n;q=max(ok,key=lambda p:p.stat().st_mtime_ns)
  rec['new_modules'].append({'module':n,'source':str(p.relative_to(R)),'source_sha256':sha(p),'compiled_source':str((O/p.name).relative_to(R)),'olean':str((O/(n+'.olean')).relative_to(R)),'olean_sha256':sha(O/(n+'.olean')),'build_receipt':str(q.relative_to(R)),'build_receipt_sha256':sha(q)})
 for n in ['TARGET-v1.md','CONTROLS-PIN-v1.md','ROOT-v1.json','ROOT-v2.json','POOL-FREEZE-CONFIRM-v1.json','FAST-DISPATCH-PLAN-SNAPSHOT-v1.md','instrument.py','pilot.py','prepare.py','audit.py','BindingFalsePrecontrols.lean','BindingFalseControls.lean']:
  rec['input_hashes'][str((D/n).relative_to(R))]=sha(D/n)
 for n,count in [('BindingFalsePrecontrols',4),('BindingFalseControls',5)]:
  ok=[q for q in O.glob(n+'-*.run.json') if (lambda x:x['exit']==1 and not x['failure'] and x['source_sha256']==sha(D/(n+'.lean')))(json.loads(q.read_text()))];assert ok;q=max(ok,key=lambda p:p.stat().st_mtime_ns)
  rec.setdefault('false_controls',[]).append({'source':str((D/(n+'.lean')).relative_to(R)),'receipt':str(q.relative_to(R)),'sha256':sha(q),'actual_false_rejections':count})
 save()
 for n,text,want in [('BothLocalStdTrue','import Std\nexample : (3:Nat)+4=7 := by decide\n',0),('BothLocalStdFalse','import Std\nexample : (3:Nat)+4=8 := by decide\n',1)]:
  (O/(n+'.lean')).write_text(text);s=run(n,want)
  if want:assert s.count('is false')==1
 (O/'BothLocalAudit.lean').write_text(instrument.source(['BindingControls'],mods,F));run('BothLocalAudit');rows=instrument.parse(F,mods,O)
 assert sum(p.stat().st_size for p in F.glob('*.gz'))<256*1024**2
 names=['ordinaryExecution_answer_congr_at','dispatch_answer_congr_at','execute_answer_congr_entries','plan_entry_budget_drop','forest_exact_at_local','ordinary_candidate_local','ordinary_candidate_below','below_ordinary_extension','forest_programs_congr_below','runPair_literal','solvePair_answer_congr_below','solvePair_sound','solvePair_conditional_cover','solvePair_minimum','solvePair_calls_strict','solvePair_trace_mass']
 required=['Universal233.BothBadLocal.'+n for n in names]
 for n in required:assert any(r['name']==n and r['kind']=='theorem' for r in rows),n
 runtime=next(r for r in rows if r['name']=='Universal233.BothBadLocal.runPair');assert runtime['kind']=='definition' and runtime['body'] is not None
 assert 'Universal233.BothBad.solvePair' in runtime['references'] and 'GenericForest.solve' in runtime['references']
 assert not any(any(bad in x for bad in ['ghost','minimumCallback','OrdinaryIH','BelowIH','ExactSolverHyp','Classical.choose']) for x in runtime['references'])
 for n in ['solvePair_conditional_cover','solvePair_minimum']:
  rr=next(r for r in rows if r['name']=='Universal233.BothBadLocal.'+n);assert 'Universal233.BothBadLocal.BelowIH' in rr['type'];assert 'GenericForest.OrdinaryIH' not in rr['type'] and 'ExactSolverHyp' not in rr['type']
 rr=next(r for r in rows if r['name']=='Universal233.BothBadLocal.ordinary_candidate_local');assert 'ForestMinCompletion.LocalOrdinaryIH' in rr['type'] and 'GenericForest.OrdinaryIH' not in rr['type']
 deps()
 for e in rec['new_modules']:pin(R/e['source'],e['source_sha256']);pin(R/e['compiled_source'],e['source_sha256']);pin(R/e['olean'],e['olean_sha256'])
 for p,h in rec['input_hashes'].items():pin(R/p,h)
 rec.update(status='PASS_AUTHOR_BOTH_BAD_LOCAL_BINDING_OPEN',new_source_modules=len(mods),stored_new_producer_occurrences=len(rows),axiom_union=sorted({a for r in rows for a in r['axiom_references']}),interfaces=required,runtime_direct_references=runtime['references'],runtime_ghost_used=False,global_ordinary_ih_premise=False,producer_files=[{'path':str(p.relative_to(R)),'sha256':sha(p)} for p in sorted(F.iterdir())],fresh_source_control_rejections=9,first_unprovided_main_call='Total fast ordinary dispatcher/current-budget recursive definition and global source/bit/payload recurrence. Minimum is scoped to original parent-refining forests; endpoint alternatives remain the surrounding hard2 dispatcher obligation.',skipped=['whole imported-pool rebuild','fresh imported-declaration audit','new extractor changes','independent semantic/interface/prose acceptance','full algorithm/base/runtime/novelty acceptance'])
 save();(D/'LATEST-REPLAY-v1.json').write_text(json.dumps({'receipt':str(O.relative_to(R)),'certificate':str(C.relative_to(R)),'sha256':sha(C)},indent=2)+'\n');print(rec['status'],len(rows),'new stored occurrences; AX=',rec['axiom_union'],flush=True)
except BaseException as e:rec.update(status='FAILED_AUTHOR_BOTH_BAD_LOCAL_AUDIT',error=repr(e));save();raise
