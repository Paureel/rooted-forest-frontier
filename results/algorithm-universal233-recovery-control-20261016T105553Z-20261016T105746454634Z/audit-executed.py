#!/usr/bin/env python3
"""Persistent recovery choose/erase/source-front audit; unchanged extractor."""
from pathlib import Path
import gzip,importlib.util,json,shutil,sys
sys.dont_write_bytecode=True
import run
D=run.D;R=run.R;O=run.O;sha=run.sha
P=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/forest_check_correspondence';m=json.loads((P/'FINAL-MANIFEST-v1.json').read_text());ip=P/'instrument.py';e=next(x for x in m['immutable_files'] if x['path']==str(ip.relative_to(R)));assert sha(ip)==e['sha256']
spec=importlib.util.spec_from_file_location('completed_control_instrument',ip);ins=importlib.util.module_from_spec(spec);spec.loader.exec_module(ins)
mods=['RCGroups','RCFilter','RCMixed','RCChoose','RCChooseBound','RCAddress','RCErase','RCInterface','RCStorage','RCControls']
F=O/'producer-records-v1';F.mkdir();C=O/'AUDIT-CERTIFICATE-v1.json';rec={'status':'RUNNING_AUTHOR','independent_credit':0,'native_full_recovery_bit_lift':False,'full_algorithm_base_novelty':'ALL_OPEN','modules':[],'controls':{},'runs':[],'instrument':{'path':str(ip.relative_to(R)),'sha256':sha(ip),'unchanged':True}}
def save():C.write_text(json.dumps(rec,indent=2)+'\n')
def pin(p,h):assert sha(p)==h,'SOURCE_PIN_MISMATCH|'+str(p)
def deps():
 for e in json.loads((D/'DEPENDENCIES-BEFORE-v1.json').read_text())['members']:
  p=R/e['path'];s=p.stat();assert sha(p)==e['sha256'] and oct(s.st_mode&0o777)==e['mode'] and s.st_ino==e['inode'] and s.st_dev==e['device'],str(p)
def cmd(n,want=0):
 before=set(O.glob(n+'-*.run.json'));s=run.run(n,want);p=next(iter(set(O.glob(n+'-*.run.json'))-before));rec['runs'].append({'path':str(p.relative_to(R)),'sha256':sha(p)});save();return s
save()
try:
 deps();(O/'audit-executed.py').write_bytes((D/'audit.py').read_bytes());(O/'run-executed.py').write_bytes((D/'run.py').read_bytes())
 pin(O/'RCGroups.lean',sha(D/'RCGroups.lean'))
 try:pin(O/'RCGroups.lean','0'*64)
 except AssertionError as e:assert 'SOURCE_PIN_MISMATCH' in str(e);rec['controls']['changed_hash']='CAUGHT'
 else:raise AssertionError('HASH_COMPARATOR_FAILED')
 for n in mods:
  p=D/(n+'.lean');pin(O/p.name,sha(p));qs=[q for q in O.glob(n+'-*.run.json') if (lambda r:r['exit']==0 and not r['stop_reasons'] and r['source_sha256']==sha(p))(json.loads(q.read_text()))];assert qs,n;q=max(qs,key=lambda p:p.stat().st_mtime_ns)
  rec['modules'].append({'module':n,'source':str(p.relative_to(R)),'source_sha256':sha(p),'compiled_source':str((O/p.name).relative_to(R)),'olean':str((O/(n+'.olean')).relative_to(R)),'olean_sha256':sha(O/(n+'.olean')),'receipt':str(q.relative_to(R)),'receipt_sha256':sha(q)})
 for n,want,count in [('RCControls',0,0),('RCFalseControls',1,16)]:
  p=D/(n+'.lean');qs=[q for q in O.glob(n+'-*.run.json') if (lambda r:r['exit']==want and not r['stop_reasons'] and r['source_sha256']==sha(p))(json.loads(q.read_text()))];assert qs;q=max(qs,key=lambda p:p.stat().st_mtime_ns);r=json.loads(q.read_text());s=gzip.open(R/r['log'],'rt').read();assert s.count('is false')==count
  if n=='RCControls':
   assert '("PASS_PERSISTENT_CONTROL_CONTROLS", 30, true)' in s
   names=json.loads((D/'CONTROLS-SUPPLEMENT-v1.json').read_text())['names'];assert len(names)==30
   for x in names:assert s.count('('+json.dumps(x)+', true)')==1,x
  rec['controls'][n]={'receipt':str(q.relative_to(R)),'sha256':sha(q),'false_diagnoses':count}
 (O/'RCAudit.lean').write_text(ins.source(['RCControls','RCStorage'],mods,F));cmd('RCAudit');rows=ins.parse(F,mods,O);names={x['name']:x for x in rows};B='OrdinaryDispatch.RecoveryControlBits.'
 required=['rawGroups_view','rawGroups_length','rawGroups_caps','copied_group_fee','closed_group_fee','closeGroups_work','groupsBits_value','groupsBits_work','allColor_value','allColor_work','filterColor_value','filterColor_view','filterColor_length','filterColor_caps','filterColor_work','uniqueTest_value','uniqueTest_work','findUnique_value','findUnique_mem','findUnique_work','mixedBits_value','rawMixed_view','rawMixed_mem','mixedBits_caps','closeMaybePair_work','pickPair_work','mixedBits_work','chooseCore_value','chooseBits_value','chooseBits_caps','choiceCells_cap','chooseCore_work','chooseBits_work','represented_choose','addressEqual_value','addressEqual_work','ownedAddressEqual_value','ownedAddressEqual_work','addressContains_value','addressContains_work','eraseBits_value','eraseBits_words','eraseBits_work_nodes','eraseBits_source_bound','represented_prepare','chosen_one_address','chosen_two_addresses','chosen_one_erase_work','chooseBits_work_decomposition','chooseBits_collector_lifetime_paid','uniqueTest_lifetime_paid','pickPair_discarded_lifetime_paid','homogeneous_refusal_lifetime_paid','address_operands_lifetime_paid','groupsCells_bound','groupsBits_retained','filterColor_retained','mixedBits_retained']
 for n in required:assert names[B+n]['kind']=='theorem',n
 required_refs={'chooseCore_work':['allColor_work','findUnique_work','mixedBits_work'],'chooseBits_work':['groupsBits_work','closeGroups_work','chooseCore_work'],'uniqueTest_work':['filterColor_work','closeGroups_work'],'findUnique_work':['uniqueTest_work'],'eraseBits_source_bound':['eraseBits_work_nodes','eraseBits_words'],'represented_prepare':['represented_choose']}
 for n,refs in required_refs.items():
  for x in refs:assert B+x in names[B+n]['references'],(n,x)
 forbidden_source_cost=['Universal233.CoreWork.local_le_cap','Universal233.CoreWork.meterRun_bound','Universal233.CoreWork.generate_work_bound','OrdinaryDispatch.RecoveryLocalWork.meterChoose_bound','OrdinaryDispatch.RecoveryLocalWork.meterErase_bound','Universal233.FinalCutRecovery.final_work_bound']
 for n in ['uniqueTest_work','chooseCore_work','chooseBits_work','eraseBits_work_nodes']:assert not any(x in names[B+n]['references'] for x in forbidden_source_cost),n
 prior=[];prior_records=[]
 for name in ['recovery_scalar_lift_20261016T095748Z','recovery_represented_initial_20261016T103025Z']:
  PM=R/'research/rmaf/algorithm/universal233/ordinary_dispatch'/name/'FINAL-MANIFEST-v1.json';pm=json.loads(PM.read_text());PO=R/pm['canonical_receipt'];pp=ins.parse(PO/'producer-records-v2',[x['module'] for x in pm['source_modules']],PO);prior+=pp;prior_records.append({'manifest':str(PM.relative_to(R)),'sha256':sha(PM),'occurrences':len(pp)})
 graph={x['name']:x for x in prior+rows}
 runtime=['closeGroups','groupsBits','allColor','filterColor','uniqueTest','findUnique','closePair','closeMaybePair','pickPair','mixedBits','chooseCore','chooseBits','addressEqual','ownedAddressEqual','addressContains','eraseBits','prepare'];refs={}
 def closure(n,seen):
  if n in seen:return
  seen.add(n);row=graph.get(n)
  if row is None or row['kind']=='theorem':return
  for x in row['references']:closure(x,seen)
 forbidden=['OrdinaryDispatch.RecoveryBits.'+x for x in ['encode','decode','viewGroup','viewTree','viewOutput']]+['OrdinaryDispatch.RecoveryInitialBits.'+x for x in ['viewInput','viewInit']]+[B+x for x in ['viewPair','viewChoice','rawGroups','rawMixed','groupFee','choiceCells','groupsCells']]+['Classical.choose']
 for n in runtime:
  row=names[B+n];assert row['kind']=='definition' and row['body'] is not None
  seen=set();closure(B+n,seen);assert not set(forbidden)&seen,(n,set(forbidden)&seen);refs[n]=row['references']
 def witness(start,goal,path):
  if start==goal:return path+[start]
  if start in path:return None
  row=graph.get(start)
  if row is None or row['kind']=='theorem':return None
  for nxt in row['references']:
   r=witness(nxt,goal,path+[start])
   if r:return r
  return None
 body_refs={'groupsBits':[B+'closeSpine','OrdinaryDispatch.RecoveryBits.copyGroup'],'filterColor':['OrdinaryDispatch.RecoveryInitialBits.ownedEqual','OrdinaryDispatch.RecoveryBits.copyGroup'],'uniqueTest':[B+'filterColor',B+'closeGroups','OrdinaryDispatch.RecoveryInitialBits.lengthOwned','OrdinaryDispatch.RecoveryInitialBits.closeBits'],'findUnique':[B+'uniqueTest','OrdinaryDispatch.RecoveryBits.copyGroup'],'pickPair':[B+'closeMaybePair'],'mixedBits':[B+'pickPair','OrdinaryDispatch.RecoveryBits.copyGroup'],'chooseCore':[B+'allColor',B+'findUnique',B+'mixedBits',B+'closePair'],'chooseBits':[B+'groupsBits',B+'chooseCore',B+'closeGroups'],'ownedAddressEqual':['OrdinaryDispatch.RecoveryInitialBits.closeBits'],'eraseBits':[B+'ownedAddressEqual','OrdinaryDispatch.RecoveryBits.copyGroup','OrdinaryDispatch.RecoveryBits.copyBits'],'prepare':['OrdinaryDispatch.RecoveryInitialBits.normalizeBits',B+'chooseBits']}
 # closeSpine belongs to the frozen initial namespace.
 body_refs['groupsBits'][0]='OrdinaryDispatch.RecoveryInitialBits.closeSpine'
 paths={}
 for n,rs in body_refs.items():
  paths[n]={}
  for x in rs:
   p=witness(B+n,x,[]);assert p,(n,x);paths[n][x]=p
 for flavor in ['missing','duplicate']:
  X=O/('producer-'+flavor+'-control-v1');X.mkdir()
  for p in F.iterdir():shutil.copyfile(p,X/p.name)
  if flavor=='missing':
   p=X/'index.json';j=json.loads(p.read_text());j['counts'].pop();p.write_text(json.dumps(j))
  else:
   p=X/'RCGroups.json.gz';j=json.load(gzip.open(p,'rt'));j.append(j[0]);gzip.open(p,'wt').write(json.dumps(j))
  try:ins.parse(X,mods,O)
  except AssertionError:rec['controls'][flavor+'_producer']='CAUGHT'
  else:raise AssertionError(flavor+'_NOT_CAUGHT')
 (O/'RCSneakyAxiom.lean').write_text('import RCStorage\naxiom controlBad : False\ntheorem controlBadUse : False := controlBad\n');cmd('RCSneakyAxiom')
 H=O/'producer-axiom-control-v1';H.mkdir();(O/'RCHostileAudit.lean').write_text(ins.source(['RCSneakyAxiom'],['RCSneakyAxiom'],H));s=cmd('RCHostileAudit',1);assert 'REJECT_PRODUCER_OCCURRENCE' in s;ins.parse(H,['RCSneakyAxiom'],O,hostile=True);rec['controls']['custom_axiom']='CAUGHT'
 for n in ['Work','RWChoose','RILifetime','RSBinaryCompare']:
  try:run.run(n)
  except AssertionError as e:assert 'REFUSE_DEPENDENCY_REBUILD' in str(e)
  else:raise AssertionError('DEPENDENCY_GUARD_FAILED')
 rec['controls']['dependency_no_rebuild_guard']=4
 deps()
 for e in rec['modules']:pin(R/e['source'],e['source_sha256']);pin(R/e['compiled_source'],e['source_sha256']);pin(R/e['olean'],e['olean_sha256'])
 assert sum(p.stat().st_size for p in O.rglob('*.gz'))<256*1024**2
 rec.update(status='PASS_AUTHOR_PERSISTENT_CHOOSE_ERASE_PREPARE_ATTEMPT_RUN_RECEIPTS_OPEN',stored_occurrences=len(rows),axiom_union=sorted({a for r in rows for a in r['axiom_references']}),interfaces=required,runtime_direct_references=refs,source_body_call_paths=paths,runtime_decode_encode_or_projection_or_desired_fee_closure_absent=True,prior_own_closure=prior_records,dependency_rebuilds=0,named_positive_checks=30,source_false_diagnoses=16,producer_files=[{'path':str(p.relative_to(R)),'sha256':sha(p)} for p in F.iterdir()],first_gap='Persistent attempt with actual represented receipts/counters and state transfer/copy/close; then step/run/fuel/pruned prefixes/receipt append and full lifetime simulation. Whole recovery bit coefficient remains open.',skipped=['dependency compilation','foreign object-pool merge','independent acceptance','native allocator/compiler/IR and runtime metadata arithmetic','persistent attempt/step/run/fuel/receipts','global ordinary/forest/Rule4/Rule5 campaigns','whole recovery bit coefficient and full2.33/base/novelty acceptance'])
 save();print(rec['status'],len(rows),'AX',rec['axiom_union'])
except BaseException as e:rec.update(status='FAIL_RETAINED',error=repr(e));save();raise
