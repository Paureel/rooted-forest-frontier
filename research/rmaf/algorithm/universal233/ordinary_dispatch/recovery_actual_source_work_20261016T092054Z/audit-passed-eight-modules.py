#!/usr/bin/env python3
"""One-shot recovery source audit; completed extractor unchanged, no dependency rebuild."""
from pathlib import Path
import gzip,importlib.util,json,shutil,sys
sys.dont_write_bytecode=True
import run
D=run.D;R=run.R;O=run.O;sha=run.sha
P=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/forest_check_correspondence';m=json.loads((P/'FINAL-MANIFEST-v1.json').read_text());ip=P/'instrument.py';pinentry=next(e for e in m['immutable_files'] if e['path']==str(ip.relative_to(R)));assert sha(ip)==pinentry['sha256']
spec=importlib.util.spec_from_file_location('completed_recovery_instrument',ip);ins=importlib.util.module_from_spec(spec);spec.loader.exec_module(ins)
mods=['RWTree','RWChoose','RWLocal','RWRun','RWInitial','RWFinal','RWInterface','RWControls'];F=O/'producer-records-v1';F.mkdir()
C=O/'AUDIT-CERTIFICATE-v1.json';rec={'status':'RUNNING_AUTHOR','independent_credit':0,'full_algorithm_base_novelty':'ALL_OPEN','modules':[],'controls':{},'runs':[],'instrument':{'path':str(ip.relative_to(R)),'sha256':sha(ip),'unchanged':True},'source_scope':'Actual CoreProgram helper/initialization/run/recovery structural source companions; arbitrary color fees explicit; literal final coloring supplied. New localCap=4*old cap and polynomial coefficient64*(old recoveryEnvelope+32), with retained2^q. No old primitive dominance premise, scalar/bit/native/full-algorithm claim.'}
def save():C.write_text(json.dumps(rec,indent=2)+'\n')
def pin(p,h):assert sha(p)==h,'SOURCE_PIN_MISMATCH|'+str(p)
def deps():
 entries=json.loads((D/'DEPENDENCIES-BEFORE-v1.json').read_text())['members']+json.loads((D/'IMPORT-COMPATIBILITY-v1.json').read_text())['transitive_early_members']
 for e in entries:
  p=R/e['path'];s=p.stat();assert sha(p)==e['sha256'] and oct(s.st_mode&0o777)==e['mode'] and s.st_ino==e['inode'] and s.st_dev==e['device'],str(p)
def cmd(n,want=0):
 before=set(O.glob(n+'-*.run.json'));s=run.run(n,want);p=next(iter(set(O.glob(n+'-*.run.json'))-before));rec['runs'].append({'path':str(p.relative_to(R)),'sha256':sha(p)});save();return s
save()
try:
 deps();(O/'audit-executed.py').write_bytes((D/'audit.py').read_bytes());(O/'run-executed.py').write_bytes((D/'run.py').read_bytes())
 pin(O/'RWTree.lean',sha(D/'RWTree.lean'))
 try:pin(O/'RWTree.lean','0'*64)
 except AssertionError as e:assert 'SOURCE_PIN_MISMATCH' in str(e);rec['controls']['changed_hash']='CAUGHT'
 else:raise AssertionError('HASH_COMPARATOR_FAILED')
 for n in mods:
  p=D/(n+'.lean');pin(O/p.name,sha(p));qs=[q for q in O.glob(n+'-*.run.json') if (lambda r:r['exit']==0 and not r['stop_reasons'] and r['source_sha256']==sha(p))(json.loads(q.read_text()))];assert qs,n;q=max(qs,key=lambda p:p.stat().st_mtime_ns)
  rec['modules'].append({'module':n,'source':str(p.relative_to(R)),'source_sha256':sha(p),'compiled_source':str((O/p.name).relative_to(R)),'olean':str((O/(n+'.olean')).relative_to(R)),'olean_sha256':sha(O/(n+'.olean')),'receipt':str(q.relative_to(R)),'receipt_sha256':sha(q)})
 for n,want,count in [('RWControls',0,0),('RWFalseControls',1,12)]:
  p=D/(n+'.lean');qs=[q for q in O.glob(n+'-*.run.json') if (lambda r:r['exit']==want and not r['stop_reasons'] and r['source_sha256']==sha(p))(json.loads(q.read_text()))];assert qs;q=max(qs,key=lambda p:p.stat().st_mtime_ns);rr=json.loads(q.read_text());s=gzip.open(R/rr['log'],'rt').read();assert s.count('is false')==count
  if n=='RWControls':
   for line in ['("PRUNED_KNOWN", [(0, 0, 1, 2, 2), (0, 0, 3, 4, 2), (2, 0, 5, 4, 0)])','("COLOR_KNOWN", 11, 19, 0)','("PASS_RECOVERY_SOURCE_CONTROLS", 15, true)']:assert line in s,line
   for case in ['unique_priority','uniform_priority','two_priority','mixed_first','root_refusal','duplicate_refusal','entire_refusal','one_continuation','literal_receipts','singleton_generate','large_budget_generate','duplicate_generate','recovery_singleton','recovery_two','recovery_refused']:assert s.count('('+json.dumps(case)+', true)')==1,case
  rec['controls'][n]={'receipt':str(q.relative_to(R)),'sha256':sha(q),'false_diagnoses':count}
 (O/'RWAudit.lean').write_text(ins.source(['RWControls'],mods,F));cmd('RWAudit');rows=ins.parse(F,mods,O);names={r['name']:r for r in rows};prefix='OrdinaryDispatch.RecoveryLocalWork.'
 required=['meterGroups_value','meterGroups_bound','meterNormalize_value','meterNormalize_bound','meterErase_value','meterErase_bound','meterMixed_value','meterMixed_bound','meterUniqueTest_bound','meterChoose_value','meterChoose_bound','choose_one_origin','choose_two_origins','meterAttempt_value','meterAttempt_bound','meterAttempt_records','meterOutput_value','meterOutput_bound','meterStep_value','meterStep_bound','meterRun_value','meterRun_records','meterRun_bound','meterRun_closed','localCap_eq_four_declared','meterBuild_value','meterBuild_coloring','meterBuild_bound','meterInitial_value','meterInitial_coloring','meterInitial_bound','meterGenerate_value','meterGenerate_bound','meterColor_value','meterColor_bound','color_sum_bound','meterRecover_value','final_source_work_bound','finalSourcePolynomial_legacy','final_source_uniform','final_source_absorbed','optimizer_recovery_once_bound','optimizer_recovery_233']
 for n in required:assert names[prefix+n]['kind']=='theorem',n
 forbidden=['Universal233.CoreWork.local_le_cap','Universal233.CoreWork.meterRun_bound','Universal233.CoreWork.generate_work_bound','Universal233.FinalCutRecovery.final_work_bound','Universal233.FinalCutRecovery.final_work_absorbed']
 for n in ['meterStep_bound','meterRun_bound','meterInitial_bound','meterGenerate_bound','final_source_work_bound']:
  r=names[prefix+n];assert not any(f in r['references'] for f in forbidden),(n,r['references'])
 required_refs={'meterInitial_bound':['meterBuild_bound'],'meterGenerate_bound':['meterRun_closed','meterInitial_bound'],'meterStep_bound':['meterNormalize_bound','meterChoose_bound','meterAttempt_bound','meterOutput_bound'],'final_source_work_bound':['meterGenerate_bound','color_sum_bound']}
 for n,rs in required_refs.items():
  for ref in rs:assert prefix+ref in names[prefix+n]['references'],(n,ref)
 runtime=['meterGroups','normalizeFee','meterNormalize','meterErase','meterMixed','meterUniqueTest','meterChoose','meterAttempt','meterOutput','meterStep','localCap','meterRun','meterBuild','meterInitial','meterGenerate','meterColor','meterRecover','finalSourcePolynomial','recoverySourceEnvelope'];refs={}
 for n in runtime:
  row=names[prefix+n];assert row['kind']=='definition' and row['body'] is not None
  assert not any(any(x in ref for x in ['OrdinaryIH','BelowIH','ExactSolverHyp','Classical.choose','minimumCallback']) for ref in row['references']);refs[n]=row['references']
 for n in ['meterStep','meterRun','meterInitial','meterGenerate','meterRecover']:
  assert not any(f in refs[n] for f in ['Universal233.CoreWork.localCharge','Universal233.CoreWork.meterGenerate','Universal233.CoreWork.meterRun']),n
 for flavor in ['missing','duplicate']:
  X=O/('producer-'+flavor+'-control');X.mkdir()
  for p in F.iterdir():shutil.copyfile(p,X/p.name)
  if flavor=='missing':
   p=X/'index.json';j=json.loads(p.read_text());j['counts'].pop();p.write_text(json.dumps(j))
  else:
   p=X/'RWTree.json.gz';j=json.load(gzip.open(p,'rt'));j.append(j[0]);gzip.open(p,'wt').write(json.dumps(j))
  try:ins.parse(X,mods,O)
  except AssertionError:rec['controls'][flavor+'_producer']='CAUGHT'
  else:raise AssertionError(flavor+'_NOT_CAUGHT')
 (O/'RWSneakyAxiom.lean').write_text('import RWControls\naxiom recoveryBad : False\ntheorem recoveryBadUse : False := recoveryBad\n');cmd('RWSneakyAxiom')
 H=O/'producer-axiom-control';H.mkdir();(O/'RWHostileAudit.lean').write_text(ins.source(['RWSneakyAxiom'],['RWSneakyAxiom'],H));s=cmd('RWHostileAudit',1);assert 'REJECT_PRODUCER_OCCURRENCE' in s;ins.parse(H,['RWSneakyAxiom'],O,hostile=True);rec['controls']['custom_axiom']='CAUGHT'
 deps()
 for e in rec['modules']:pin(R/e['source'],e['source_sha256']);pin(R/e['compiled_source'],e['source_sha256']);pin(R/e['olean'],e['olean_sha256'])
 assert sum(p.stat().st_size for p in O.rglob('*.gz'))<256*1024**2
 rec.update(status='PASS_AUTHOR_ACTUAL_RECOVERY_SOURCE_UNIT_BIT_NATIVE_OPEN',stored_occurrences=len(rows),axiom_union=sorted({a for r in rows for a in r['axiom_references']}),interfaces=required,runtime_direct_references=refs,forbidden_declared_cost_imports_absent=forbidden,dependency_rebuilds=0,source_false_diagnoses=12,producer_files=[{'path':str(p.relative_to(R)),'sha256':sha(p)} for p in F.iterdir()],skipped=['scientific dependency compilation','binary reference import/merge','fresh nonauthor semantic/source/interface/prose acceptance','scalar bit and native compiler/runtime correspondence','pure polynomial recovery-time assertion: retained2^q source prefixes','ordinary solve/global recurrence/Rule5/full2.33/base/novelty acceptance'])
 save();print(rec['status'],len(rows),'AX',rec['axiom_union'])
except BaseException as e:rec.update(status='FAIL_RETAINED',error=repr(e));save();raise
