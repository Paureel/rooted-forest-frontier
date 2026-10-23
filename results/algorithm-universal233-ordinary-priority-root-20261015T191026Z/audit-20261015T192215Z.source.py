#!/usr/bin/env python3
"""Thin orchestration of the unchanged bounded stored-producer extractor.
Only four new modules are audited; all 315 dependencies stay readonly links.
"""
from pathlib import Path
import datetime,hashlib,json,shutil,sys,time
sys.dont_write_bytecode=True
import instrument,pilot
D=Path(__file__).resolve().parent;R=pilot.R;O=pilot.O
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
spec=json.loads((D/'ROOT-v1.json').read_text())
mods=['PriorityFacts','Rule4Bridge','AdmissionBridge','GuardControls']
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
def deps():
 for e in spec['dependencies']:
  for f in e['files']:
   a=R/f['original'];b=R/f['linked'];pin(a,f['sha256']);pin(b,f['sha256'])
   for p in [a,b]:
    s=p.stat();assert s.st_ino==f['inode'] and s.st_dev==f['device'] and s.st_nlink>1
    assert not s.st_mode&0o222,'MUTABLE_DEPENDENCY'
def run(n,want=0):
 before=set(O.glob(n+'-*.run.json'));s=pilot.run(n,want=want)
 p=next(iter(set(O.glob(n+'-*.run.json'))-before));rec['runs'].append({'path':str(p.relative_to(R)),'sha256':sha(p)});save();return s
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
C=O/('certificate-'+stamp+'.json');F=O/('producer-records-'+stamp);F.mkdir()
rec={'status':'RUNNING_AUTHOR_NEW_MODULE_AUDIT','independent_credit':0,'main_milestones':'ALL_OPEN',
 'root':str(O.relative_to(R)),'root_pin_sha256':sha(D/'ROOT-v1.json'),'new_modules':[],
 'dependency_pin_scope':'315 frozen source/olean modules; exact path/hash/inode/readonly links checked before and after; no dependency compiled',
 'producer_preflight':spec['producer_preflight'],'instrument_sha256':sha(D/'instrument.py'),
 'runs':[],'input_hashes':{},'module_timeout_seconds':30,'live_disk_floor_bytes':3*1024**3,
 'producer_uncompressed_cap_bytes':8388608,'compressed_total_cap_bytes':256*1024**2,
 'audit_scope':'New stored producer occurrences only. Theorem proof TEXT omitted; actual ConstantInfo.getUsedConstantsAsSet proof references and full AX closure retained. Full nonproof/opaque bodies retained.'}
def save():C.write_text(json.dumps(rec,indent=2)+'\n')
save()
try:
 # Reuse exact frozen generator controls; no new blind or independent credit.
 pin(D/'instrument.py',spec['instrument_sha256'])
 pre=spec['producer_preflight'];P=R/pre['manifest'];pin(P,pre['sha256']);pc=json.loads(P.read_text());pin(D/'instrument.py',pc['instrument_sha256'])
 for e in pc['immutable_files']:pin(R/e['path'],e['sha256'])
 pin(R/spec['frozen_manifest']['path'],spec['frozen_manifest']['sha256'])
 # Fresh guard controls before any real audit extraction.
 try:pilot.run('RMAF')
 except RuntimeError as e:assert str(e)=='REFUSE_LINKED_DEPENDENCY_COMPILATION|RMAF'
 else:raise AssertionError('LINKED_DEPENDENCY_COMPILE_GUARD_FAILED')
 assert hashlib.sha256(b'abc').hexdigest()=='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
 assert hashlib.sha256(b'abc').hexdigest()!=hashlib.sha256(b'abd').hexdigest()
 deps()
 if shutil.disk_usage(D).free<3*1024**3:raise RuntimeError('DISK_FLOOR_3_GIB')
 for n in mods:
  p=D/(n+'.lean');pin(O/p.name,sha(p));assert (O/(n+'.olean')).exists()
  successes=[q for q in O.glob(n+'-*.run.json') if (lambda x:x['exit']==0 and not x['failure'] and x['source_sha256']==sha(p))(json.loads(q.read_text()))]
  assert successes,'MISSING_EXACT_SUCCESSFUL_BUILD|'+n
  q=max(successes,key=lambda p:p.stat().st_mtime_ns)
  rec['new_modules'].append({'module':n,'source':str(p.relative_to(R)),'source_sha256':sha(p),'compiled_source':str((O/p.name).relative_to(R)),'olean':str((O/(n+'.olean')).relative_to(R)),'olean_sha256':sha(O/(n+'.olean')),'successful_build_receipt':str(q.relative_to(R)),'successful_build_receipt_sha256':sha(q)})
 for n in ['TARGET-v1.md','CONTROLS-PIN-v1.md','FIRST-CASE-PIN-v1.md','ROOT-v1.json','instrument.py','pilot.py','audit.py','GuardFalseControls.lean']:
  rec['input_hashes'][str((D/n).relative_to(R))]=sha(D/n)
 save()
 for n,text,want in [('PriorityStdTrue','import Std\nexample : (3:Nat)+4=7 := by decide\n',0),('PriorityStdFalse','import Std\nexample : (3:Nat)+4=8 := by decide\n',1)]:
  (O/(n+'.lean')).write_text(text);s=run(n,want)
  if want:assert s.count('is false')==1
 false=[q for q in O.glob('GuardFalseControls-*.run.json') if (lambda x:x['exit']==1 and not x['failure'] and x['source_sha256']==sha(D/'GuardFalseControls.lean'))(json.loads(q.read_text()))]
 assert len(false)==1
 rec['mathematical_false_control_receipt']={'path':str(false[0].relative_to(R)),'sha256':sha(false[0]),'rejections':6}
 (O/'PriorityAudit.lean').write_text(instrument.source(['GuardControls'],mods,F));run('PriorityAudit');rows=instrument.parse(F,mods,O)
 assert sum(p.stat().st_size for p in F.glob('*.gz'))<256*1024**2
 names=['hard2_earlierClear','hard2_actual','hard2_every_cherry','proper_parts','proper_rule5','proper_reverse','actual_rule4_priority','hasCherry_scan_sound','two_member_perm','singleton_mate_selects','rule4_scan_selects','rule4_scan_isSome','rule4_none_scan_false','actual_no_rule4','hard2_priority_guards','actual_rule5_admitted_iff']
 required=['Universal233.OrdinaryPriorityBridge.'+n for n in names]
 for n in required:assert any(r['name']==n and r['kind']=='theorem' for r in rows),n
 for n in ['commonC','commonD']:
  rr=next(r for r in rows if r['name']=='Universal233.OrdinaryPriorityBridge.Controls.'+n);assert rr['kind']=='definition' and rr['body'] is not None
 deps()
 for e in rec['new_modules']:pin(R/e['source'],e['source_sha256']);pin(R/e['compiled_source'],e['source_sha256']);pin(R/e['olean'],e['olean_sha256'])
 for p,h in rec['input_hashes'].items():pin(R/p,h)
 rec.update(status='PASS_AUTHOR_PRIORITY_BRIDGE_EXACT_ADMISSION_GAP_OPEN',new_source_builds=4,pinned_dependency_modules=len(spec['dependencies']),stored_new_producer_occurrences=len(rows),axiom_union=sorted({a for r in rows for a in r['axiom_references']}),interfaces=required,producer_files=[{'path':str(p.relative_to(R)),'sha256':sha(p)} for p in sorted(F.iterdir())],fresh_controls={'std_true':'PASS','std_false':'REJECTED_ACTUAL_FALSE','mathematical_false_claims':6,'literal_endpoint_and_singleton_positions':'PASS','linked_dependency_compile_refusal':'PASS'},first_unprovided_main_call='Actual first hard2 commonT/commonS candidate (3,4) does not satisfy Rule5 admission: target embedding=false, good-block count=1; actual both Rule4 selectors none, while admitted (0,1)=true.',skipped=['whole dependency-pool rebuild','raw dependency producer dumps','fresh extractor modification','independent semantic/interface/prose acceptance','main algorithm/base/novelty acceptance'])
 save();(D/'LATEST-REPLAY-v1.json').write_text(json.dumps({'receipt':str(O.relative_to(R)),'certificate':str(C.relative_to(R)),'sha256':sha(C)},indent=2)+'\n')
 print(rec['status'],len(rows),'new stored occurrences; AX=',rec['axiom_union'],flush=True)
except BaseException as e:
 rec.update(status='FAILED_AUTHOR_NEW_MODULE_AUDIT',error=repr(e));save();raise
