#!/usr/bin/env python3
"""One-shot optimizer source audit wrapping the unchanged completed producer instrument."""
from pathlib import Path
import gzip,hashlib,importlib.util,json,shutil,sys
sys.dont_write_bytecode=True
import run
D=run.D;R=run.R;O=run.O;sha=run.sha
E=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/early_selection_local_work/FINAL-MANIFEST-v1.json';em=json.loads(E.read_text());ip=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/forest_check_correspondence/instrument.py';entry=next(e for e in em['original_files'] if e['path']==str(ip.relative_to(R)));assert sha(ip)==entry['sha256']
spec=importlib.util.spec_from_file_location('completed_optimizer_instrument',ip);ins=importlib.util.module_from_spec(spec);spec.loader.exec_module(ins)
mods=['OWScan','OWRecovery','OWOptimize','OWControls'];F=O/'producer-records-v1';F.mkdir()
rec={'status':'RUNNING_AUTHOR','independent_credit':0,'full_algorithm_base_novelty':'ALL_OPEN','modules':[],'controls':{},'instrument':{'path':str(ip.relative_to(R)),'sha256':sha(ip),'unchanged':True},'source_boundary':'Derived optimizer wrapper plus raw recovery guard/color/length/head work; solve callback w explicit; CoreWork.initialCharge/localCharge source interpretation OPEN; no scalar/bit/native interpretation.','runs':[]}
C=O/'AUDIT-CERTIFICATE-v1.json'
def save():C.write_text(json.dumps(rec,indent=2)+'\n')
def deps():
 for f in ['DEPENDENCIES-BEFORE-v1.json','TRANSITIVE-EARLY-DEPS-v1.json']:
  for e in json.loads((D/f).read_text())['members']:
   p=R/e['path'];s=p.stat();assert sha(p)==e['sha256'] and oct(s.st_mode&0o777)==e['mode'] and s.st_ino==e['inode'] and s.st_dev==e['device'],str(p)
def cmd(n,want=0):
 before=set(O.glob(n+'-*.run.json'));s=run.run(n,want);p=next(iter(set(O.glob(n+'-*.run.json'))-before));rec['runs'].append({'path':str(p.relative_to(R)),'sha256':sha(p)});save();return s
save()
try:
 deps();(O/'audit-executed.py').write_bytes((D/'audit.py').read_bytes());(O/'run-executed.py').write_bytes((D/'run.py').read_bytes())
 assert hashlib.sha256(b'abc').hexdigest()=='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
 def pin(p,h):assert sha(p)==h,'SOURCE_PIN_MISMATCH'
 pin(O/'OWScan.lean',sha(D/'OWScan.lean'))
 try:pin(O/'OWScan.lean','0'*64)
 except AssertionError as e:assert str(e)=='SOURCE_PIN_MISMATCH';rec['controls']['changed_hash']='CAUGHT'
 else:raise AssertionError('HASH_COMPARATOR_FAILED')
 for n in mods:
  p=D/(n+'.lean');pin(O/p.name,sha(p));qs=[q for q in O.glob(n+'-*.run.json') if (lambda r:r['exit']==0 and not r['stop_reasons'] and r['source_sha256']==sha(p))(json.loads(q.read_text()))];assert qs,n;q=max(qs,key=lambda p:p.stat().st_mtime_ns)
  rec['modules'].append({'module':n,'source':str(p.relative_to(R)),'source_sha256':sha(p),'compiled_source':str((O/p.name).relative_to(R)),'olean':str((O/(n+'.olean')).relative_to(R)),'olean_sha256':sha(O/(n+'.olean')),'receipt':str(q.relative_to(R)),'receipt_sha256':sha(q)})
 for n,want,count in [('OWControls',0,0),('OWFalseControls',1,10)]:
  p=D/(n+'.lean');qs=[q for q in O.glob(n+'-*.run.json') if (lambda r:r['exit']==want and not r['stop_reasons'] and r['source_sha256']==sha(p))(json.loads(q.read_text()))];assert qs;q=max(qs,key=lambda p:p.stat().st_mtime_ns);rr=json.loads(q.read_text());s=gzip.open(R/rr['log'],'rt').read();assert s.count('is false')==count
  if n=='OWControls':
   for line in ['("SCAN_KNOWN", [(0, false), (1, true)], 24, 27)','("FAIL_KNOWN", [(0, false), (1, false), (2, false)], 38, 41)','("PASS_OPTIMIZER_LOCAL_CONTROLS", 10, true)','("RAW_GUARD_WORK", 87, 34641)']:assert line in s,line
   assert s.count(', true)')==11,s
  rec['controls'][n]={'receipt':str(q.relative_to(R)),'sha256':sha(q),'false_diagnoses':count}
 (O/'OWAudit.lean').write_text(ins.source(['OWControls'],mods,F));cmd('OWAudit');rows=ins.parse(F,mods,O);names={r['name']:r for r in rows}
 required=['meterPreflight_value','meterPreflight_bound','meterScan_value','meterScan_accounting','meterScan_administration','actual_scanned_budget_cap','meterInputCheck_value','meterInputCheck_bound','recovery_guard_covered','meterRecovery_value','meterRecovery_le_legacy','recovery_counter_bound','meterFinish_value','meterFinish_bound','meterOptimize_value','actual_wrapper_fees','wrapper_polynomial','conditional_233_derived_wrapper']
 for n in required:assert names['OrdinaryDispatch.OptimizerLocalWork.'+n]['kind']=='theorem',n
 runtime=['meterLength','meterPreflight','meterScan','meterInputCheck','meterRecovery','meterFinish','meterOptimize'];refs={}
 for n in runtime:
  r=names['OrdinaryDispatch.OptimizerLocalWork.'+n];assert r['kind']=='definition' and r['body'] is not None
  assert not any(any(x in ref for x in ['OrdinaryIH','BelowIH','ExactSolverHyp','Classical.choose','minimumCallback']) for ref in r['references']);refs[n]=r['references']
 for flavor in ['missing','duplicate']:
  X=O/('producer-'+flavor+'-control');X.mkdir()
  for p in F.iterdir():shutil.copyfile(p,X/p.name)
  if flavor=='missing':
   p=X/'index.json';j=json.loads(p.read_text());j['counts'].pop();p.write_text(json.dumps(j))
  else:
   p=X/'OWScan.json.gz';j=json.load(gzip.open(p,'rt'));j.append(j[0]);gzip.open(p,'wt').write(json.dumps(j))
  try:ins.parse(X,mods,O)
  except AssertionError:rec['controls'][flavor+'_producer']='CAUGHT'
  else:raise AssertionError(flavor+'_NOT_CAUGHT')
 (O/'OWSneakyAxiom.lean').write_text('import OWControls\naxiom optimizerBad : False\ntheorem optimizerBadUse : False := optimizerBad\n');cmd('OWSneakyAxiom')
 H=O/'producer-axiom-control';H.mkdir();(O/'OWHostileAudit.lean').write_text(ins.source(['OWSneakyAxiom'],['OWSneakyAxiom'],H));s=cmd('OWHostileAudit',1);assert 'REJECT_PRODUCER_OCCURRENCE' in s;ins.parse(H,['OWSneakyAxiom'],O,hostile=True);rec['controls']['custom_axiom']='CAUGHT'
 deps()
 for e in rec['modules']:pin(R/e['source'],e['source_sha256']);pin(R/e['compiled_source'],e['source_sha256']);pin(R/e['olean'],e['olean_sha256'])
 rec.update(status='PASS_AUTHOR_OPTIMIZER_WRAPPER_RECOVERY_PROVIDER_OPEN',stored_occurrences=len(rows),axiom_union=sorted({a for r in rows for a in r['axiom_references']}),interfaces=required,runtime_direct_references=refs,dependency_rebuilds=0,source_false_diagnoses=10,producer_files=[{'path':str(p.relative_to(R)),'sha256':sha(p)} for p in F.iterdir()],skipped=['blanket toolkit suite: no toolkit changed','scientific dependency compilation','fresh nonauthor source/interface/prose acceptance','CoreWork.initialCharge/localCharge fine source-provider interpretation','actual solve/bit/global recurrence work','native compiler/runtime and full algorithm/base/novelty acceptance'])
 save();print(rec['status'],len(rows),'AX',rec['axiom_union'])
except BaseException as e:rec.update(status='FAIL_RETAINED',error=repr(e));save();raise
