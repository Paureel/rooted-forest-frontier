#!/usr/bin/env python3
"""One-shot early continuation audit wrapping the exact completed instrument unchanged."""
from pathlib import Path
import gzip,hashlib,importlib.util,json,shutil,sys,time
sys.dont_write_bytecode=True
import run
D=run.D;A=run.A;R=run.R;O=run.O;sha=run.sha
P=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/forest_check_correspondence'
manifest=json.loads((P/'FINAL-MANIFEST-v1.json').read_text());entry=next(x for x in manifest['immutable_files'] if x['path']==str((P/'instrument.py').relative_to(R)));assert sha(P/'instrument.py')==entry['sha256']
loader=importlib.util.spec_from_file_location('early_completed_instrument',P/'instrument.py');ins=importlib.util.module_from_spec(loader);loader.loader.exec_module(ins)
mods=run.mods+['ERInterface','ERControls'];F=O/'producer-records-v1';F.mkdir(exist_ok=True)
rec={'status':'RUNNING_AUTHOR','independent_credit':0,'main_milestones':'ALL_OPEN','scope':'actual structural unit-source upper evaluator; no binary/native/compiled trace correspondence','instrument':{'path':str((P/'instrument.py').relative_to(R)),'sha256':sha(P/'instrument.py'),'unchanged':True},'modules':[],'controls':{},'skipped':['blanket toolkit battery: no toolkit changed','dependency rebuild: exact licensed readonly module closure reused','fresh nonauthor semantic/interface review','full algorithm/global recurrence/base/novelty acceptance','binary scalar and native compiler semantics']}
cert=O/'AUDIT-CERTIFICATE-v1.json'
def save():cert.write_text(json.dumps(rec,indent=2)+'\n')
def unchanged():
 for e in json.loads((D/'DEPENDENCY-INITIAL-v1.json').read_text())['members']:
  p=R/e['path'];st=p.stat();assert sha(p)==e['sha256'] and oct(st.st_mode&0o777)==e['mode'] and st.st_ino==e['inode'] and st.st_dev==e['device'],str(p)
 for e in json.loads((O/'DEPENDENCY-SNAPSHOTS-v1.json').read_text()):
  p=R/e['original'];st=p.stat();assert sha(p)==e['sha256'] and oct(st.st_mode&0o777)==e['mode'] and st.st_ino==e['inode'] and st.st_dev==e['device'];q=R/e['snapshot'];assert sha(q)==e['sha256'] and not q.stat().st_mode&0o222
save()
try:
 unchanged()
 # Known exact hash/comparator control, followed by its deliberately changed twin.
 assert hashlib.sha256(b'abc').hexdigest()=='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
 def pin(p,h):assert sha(p)==h,'SOURCE_PIN_MISMATCH'
 p=O/'ERControls.lean';pin(p,sha(D/'ERControls.lean'))
 try:pin(p,'0'*64)
 except AssertionError as e:assert str(e)=='SOURCE_PIN_MISMATCH';rec['controls']['changed_source_hash']='CAUGHT'
 else:raise AssertionError('HASH_COMPARATOR_FAILED')
 for n in mods:
  p=O/(n+'.lean');origin=(A if n in run.mods else D)/(n+'.lean');assert sha(p)==sha(origin)
  receipts=[q for q in O.glob(n+'-*.run.json') if (lambda r:r['exit']==0 and not r['stop_reasons'] and r['source_sha256']==sha(p))(json.loads(q.read_text()))];assert receipts,n
  q=max(receipts,key=lambda p:p.stat().st_mtime_ns);rec['modules'].append({'module':n,'source':str(origin.relative_to(R)),'compiled_source':str(p.relative_to(R)),'source_sha256':sha(p),'olean':str((O/(n+'.olean')).relative_to(R)),'olean_sha256':sha(O/(n+'.olean')),'receipt':str(q.relative_to(R)),'receipt_sha256':sha(q)})
 for n,want,count in [('ERControls',0,0),('ERFalseControls',1,10)]:
  p=O/(n+'.lean');qs=[q for q in O.glob(n+'-*.run.json') if (lambda r:r['exit']==want and not r['stop_reasons'] and r['source_sha256']==sha(p))(json.loads(q.read_text()))];assert qs,n;q=max(qs,key=lambda p:p.stat().st_mtime_ns);r=json.loads(q.read_text());out=gzip.open(R/r['log'],'rt').read();assert out.count('is false')==count
  if n=='ERControls':
   for line in ['("ordinary", [true, false])','("pretest", [1, 3, 2])','("crossed", [false, false, false, false, false, false, false], [6, 5, 4, 3, 2, 1, 0])','("toy", some 1, 24, [2, 1, 0], [(2, 1)])','("orientations", [1, 3, 4, 5, 6, 7, 9])','("primitive_work_leaf", 16)']:assert line in out,line
  rec['controls'][n]={'receipt':str(q.relative_to(R)),'sha256':sha(q),'false_diagnoses':count}
 (O/'ERAudit.lean').write_text(ins.source(['ERControls'],mods,F));run.run('ERAudit');rows=ins.parse(F,mods,O);byname={r['name']:r for r in rows}
 required=['meterOrdinaryProper_value','meterOrdinaryProper_bound','meterPendant_value','meterPendant_bound','meterPretest_value','meterPretest_bound','meterBest_trace','candidate_address','meterSelect_value','meterSelect_bound','rawChoice_head','rawChoices_length','meterRawChoices_value','meterRawChoices_bound','meterRule4Select_value','meterRule4Select_bound','meterEarly_value','meterEarly_bound','meterFront_value','meterFront_bound','front_found_solve','front_rejected_binding','weightedFront_bound','meterFirstChoice_none_checks','cherry_select_envelope','rule4_select_envelope','earlier_clear_primitive_envelopes']
 for n in required:assert byname['OrdinaryDispatch.EarlyLocalWork.'+n]['kind']=='theorem',n
 runtime=['meterOrdinaryProper','meterPendant','meterBest','meterPretest','meterCherryCandidates','meterSelect','meterRule4Priority','meterLocalGuard','meterRawR','meterRawAC','meterRawAB','meterRawChoices','meterFirstChoice','meterRule4Select','meterEarly','meterFront']
 for n in runtime:
  e=byname['OrdinaryDispatch.EarlyLocalWork.'+n];assert e['kind']=='definition' and e['body'] is not None
  assert not any(any(bad in r for bad in ['OrdinaryIH','BelowIH','ExactSolverHyp','Classical.choose','minimumCallback']) for r in e['references']),n
 # Parser corruption twins: mutate only copies of exact emitted files.
 M=O/'producer-missing-control';M.mkdir();
 for p in F.iterdir():shutil.copyfile(p,M/p.name)
 idx=json.loads((M/'index.json').read_text());idx['counts'].pop();(M/'index.json').write_text(json.dumps(idx))
 try:ins.parse(M,mods,O)
 except AssertionError:rec['controls']['missing_producer']='CAUGHT'
 else:raise AssertionError('MISSING_PRODUCER_NOT_CAUGHT')
 X=O/'producer-duplicate-control';X.mkdir()
 for p in F.iterdir():shutil.copyfile(p,X/p.name)
 p=next(X.glob('EL*.json.gz'));rs=json.load(gzip.open(p,'rt'));rs.append(rs[0]);gzip.open(p,'wt').write(json.dumps(rs))
 try:ins.parse(X,mods,O)
 except AssertionError:rec['controls']['duplicate_occurrence']='CAUGHT'
 else:raise AssertionError('DUPLICATE_NOT_CAUGHT')
 # Execute a real custom-axiom plant through Lean's collector and same parser.
 (O/'ERSneakyAxiom.lean').write_text('import ERControls\naxiom earlyBadAxiom : False\ntheorem earlyBadTheorem : False := earlyBadAxiom\n');run.run('ERSneakyAxiom')
 H=O/'producer-axiom-control';H.mkdir();(O/'ERHostileAudit.lean').write_text(ins.source(['ERSneakyAxiom'],['ERSneakyAxiom'],H));bad=run.run('ERHostileAudit',1);assert 'REJECT_PRODUCER_OCCURRENCE' in bad;ins.parse(H,['ERSneakyAxiom'],O,hostile=True);rec['controls']['custom_axiom']='CAUGHT'
 unchanged()
 rec.update(status='PASS_AUTHOR_ACTUAL_EARLY_UNIT_SCALAR_OPEN',stored_new_occurrences=len(rows),axiom_union=sorted({a for r in rows for a in r['axiom_references']}),interfaces=['OrdinaryDispatch.EarlyLocalWork.'+n for n in required],runtime_direct_references={n:byname['OrdinaryDispatch.EarlyLocalWork.'+n]['references'] for n in runtime},producer_files=[{'path':str(p.relative_to(R)),'sha256':sha(p)} for p in sorted(F.iterdir())],dependency_rebuilds=0,dependency_members_identity_verified=5711)
 save();print(rec['status'],len(rows),'AX',rec['axiom_union'])
except BaseException as e:rec.update(status='FAIL_RETAINED',error=repr(e));save();raise
