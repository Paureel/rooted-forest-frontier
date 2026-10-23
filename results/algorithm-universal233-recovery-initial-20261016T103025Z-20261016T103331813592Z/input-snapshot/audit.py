#!/usr/bin/env python3
"""Represented initializer and normalizer audit; no dependency rebuild."""
from pathlib import Path
import gzip,importlib.util,json,shutil,sys
sys.dont_write_bytecode=True
import run
D=run.D;R=run.R;O=run.O;sha=run.sha
P=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/forest_check_correspondence';m=json.loads((P/'FINAL-MANIFEST-v1.json').read_text());ip=P/'instrument.py';e=next(x for x in m['immutable_files'] if x['path']==str(ip.relative_to(R)));assert sha(ip)==e['sha256']
spec=importlib.util.spec_from_file_location('completed_initial_instrument',ip);ins=importlib.util.module_from_spec(spec);spec.loader.exec_module(ins)
mods=['RIWords','RIBudget','RITree','RIBuild','RIInitial','RIInterface','RINormalize','RINormBound','RILifetime','RIControls']
F=O/'producer-records-v2';F.mkdir();C=O/'AUDIT-CERTIFICATE-v2.json';rec={'status':'RUNNING_AUTHOR','independent_credit':0,'native_full_recovery_bit_lift':False,'full_algorithm_base_novelty':'ALL_OPEN','modules':[],'controls':{},'runs':[],'instrument':{'path':str(ip.relative_to(R)),'sha256':sha(ip),'unchanged':True}}
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
 pin(O/'RIWords.lean',sha(D/'RIWords.lean'))
 try:pin(O/'RIWords.lean','0'*64)
 except AssertionError as e:assert 'SOURCE_PIN_MISMATCH' in str(e);rec['controls']['changed_hash']='CAUGHT'
 else:raise AssertionError('HASH_COMPARATOR_FAILED')
 for n in mods:
  p=D/(n+'.lean');pin(O/p.name,sha(p));qs=[q for q in O.glob(n+'-*.run.json') if (lambda r:r['exit']==0 and not r['stop_reasons'] and r['source_sha256']==sha(p))(json.loads(q.read_text()))];assert qs,n;q=max(qs,key=lambda p:p.stat().st_mtime_ns)
  rec['modules'].append({'module':n,'source':str(p.relative_to(R)),'source_sha256':sha(p),'compiled_source':str((O/p.name).relative_to(R)),'olean':str((O/(n+'.olean')).relative_to(R)),'olean_sha256':sha(O/(n+'.olean')),'receipt':str(q.relative_to(R)),'receipt_sha256':sha(q)})
 for n,want,count in [('RIControls',0,0),('RIFalseControls',1,12)]:
  p=D/(n+'.lean');qs=[q for q in O.glob(n+'-*.run.json') if (lambda r:r['exit']==want and not r['stop_reasons'] and r['source_sha256']==sha(p))(json.loads(q.read_text()))];assert qs;q=max(qs,key=lambda p:p.stat().st_mtime_ns);r=json.loads(q.read_text());s=gzip.open(R/r['log'],'rt').read();assert s.count('is false')==count
  if n=='RIControls':
   assert '("PASS_REPRESENTED_INITIAL_CONTROLS", 20, true)' in s
   for x in ['singleton','tri_large_budget','tri_small_budget','duplicate_refusal','padding_duplicate','source_refinement','missing_color','head_color','empty_block','address_append','input_copy','leaves_copy','lifetime_word','owned_equal','input_copy_fee','input_close_fee','count_width_required','homogeneous_merge','normalized_tri','normalizer_source']:assert s.count('('+json.dumps(x)+', true)')==1,x
  rec['controls'][n]={'receipt':str(q.relative_to(R)),'sha256':sha(q),'false_diagnoses':count}
 (O/'RIAudit.lean').write_text(ins.source(['RIControls'],mods,F));cmd('RIAudit');rows=ins.parse(F,mods,O);names={x['name']:x for x in rows};B='OrdinaryDispatch.RecoveryInitialBits.'
 required=['closeBits_work','closeArrays_work','closeForest_work','ownedEqual_value','ownedEqual_work','ownedContains_value','ownedContains_work','ownedNodup_value','ownedNodup_work','ownedColor_value','ownedColor_length','ownedColor_work','stepLength_value','stepLength_work','lengthOwned_value','lengthOwned_work','ownedSubtract_value','ownedSubtract_work','clipOwned_value','clipOwned_work','copyInput_value','copyInput_work','closeInput_work','leafArrays_value','leafArrays_work','appendAddress_value','build_value','build_words','build_work','initialCore_value','initialCore_work','initializeBits_value','initializeBits_work','initializeBits_some','initializeBits_refused','initializeBits_output_words','initializeBits_retained_cells','represented_initialization','normalizeBits_value','normalizeBits_words','mergeGroups_work','assemble_work','normalizeBits_work_nodes','normalizeBits_source_bound','initializeBits_work_decomposition','initializeBits_input_lifetime_paid','initialCore_first_leaves_lifetime_paid','stepLength_temporary_lifetime_paid','ownedSubtract_temporary_lifetime_paid','merged_children_lifetime_paid']
 for n in required:assert names[B+n]['kind']=='theorem',n
 required_refs={'initializeBits_value':['initialCore_value'],'initialCore_work':['leafArrays_work','ownedNodup_work','closeArrays_work','clipOwned_work','build_work'],'initializeBits_work':['initialCore_work','copyInput_work','closeInput_work','closeForest_work'],'normalizeBits_work_nodes':['assemble_work','normalizeBits_words'],'normalizeBits_source_bound':['normalizeBits_work_nodes']}
 for n,refs in required_refs.items():
  for x in refs:assert B+x in names[B+n]['references'],(n,x)
 forbidden_source_cost=['Universal233.CoreWork.local_le_cap','Universal233.CoreWork.meterRun_bound','Universal233.CoreWork.generate_work_bound','OrdinaryDispatch.RecoveryLocalWork.meterInitial_bound','Universal233.FinalCutRecovery.final_work_bound']
 for n in ['initialCore_work','initializeBits_work','build_work','normalizeBits_work_nodes']:assert not any(x in names[B+n]['references'] for x in forbidden_source_cost),n
 # Exact prior own producer records extend runtime closure checks without merging object pools.
 PM=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/recovery_scalar_lift_20261016T095748Z/FINAL-MANIFEST-v1.json';pm=json.loads(PM.read_text());PO=R/pm['canonical_receipt'];prior=ins.parse(PO/'producer-records-v2',[x['module'] for x in pm['source_modules']],PO);graph={x['name']:x for x in prior+rows}
 runtime=['closeBits','closeArrays','closeForest','ownedEqual','ownedContains','ownedNodup','ownedColor','zeroBits','takeCopy','stepLength','lengthOwned','ownedSubtract','clipOwned','copyInput','closeInput','appendRefs','closeSpine','leafArrays','appendAddress','build','initialCore','initializeBits','closeGroup','closeTree','mergeGroups','assemble','normalizeBits'];refs={}
 def closure(n,seen):
  if n in seen:return
  seen.add(n);row=graph.get(n)
  if row is None or row['kind']=='theorem':return
  for x in row['references']:closure(x,seen)
 forbidden=['OrdinaryDispatch.RecoveryBits.'+x for x in ['encode','decode','viewGroup','viewTree','viewOutput']]+[B+'viewInput',B+'viewInit','Classical.choose']
 for n in runtime:
  row=names[B+n];assert row['kind']=='definition' and row['body'] is not None
  seen=set();closure(B+n,seen);assert not set(forbidden)&seen,(n,set(forbidden)&seen);refs[n]=row['references']
 body_refs={'initializeBits':['copyInput','initialCore','closeInput','closeForest','closeBits'],'initialCore':['leafArrays','ownedNodup','closeArrays','clipOwned','build'],'stepLength':['closeBits'],'ownedSubtract':['closeBits'],'build':['ownedColor','appendAddress','closeBits'],'assemble':['ownedEqual','mergeGroups','closeTree']}
 def witness(start,goal,path):
  if start==goal:return path+[start]
  if start in path:return None
  row=graph.get(start)
  if row is None or row['kind']=='theorem':return None
  for nxt in row['references']:
   r=witness(nxt,goal,path+[start])
   if r:return r
  return None
 call_witnesses={}
 for n,rs in body_refs.items():
  call_witnesses[n]={}
  for x in rs:
   path=witness(B+n,B+x,[]);assert path,(n,x);call_witnesses[n][x]=path
 for flavor in ['missing','duplicate']:
  X=O/('producer-'+flavor+'-control-v2');X.mkdir()
  for p in F.iterdir():shutil.copyfile(p,X/p.name)
  if flavor=='missing':
   p=X/'index.json';j=json.loads(p.read_text());j['counts'].pop();p.write_text(json.dumps(j))
  else:
   p=X/'RIWords.json.gz';j=json.load(gzip.open(p,'rt'));j.append(j[0]);gzip.open(p,'wt').write(json.dumps(j))
  try:ins.parse(X,mods,O)
  except AssertionError:rec['controls'][flavor+'_producer']='CAUGHT'
  else:raise AssertionError(flavor+'_NOT_CAUGHT')
 (O/'RISneakyAxiom.lean').write_text('import RIControls\naxiom initialBad : False\ntheorem initialBadUse : False := initialBad\n');cmd('RISneakyAxiom')
 H=O/'producer-axiom-control-v2';H.mkdir();(O/'RIHostileAudit.lean').write_text(ins.source(['RISneakyAxiom'],['RISneakyAxiom'],H));s=cmd('RIHostileAudit',1);assert 'REJECT_PRODUCER_OCCURRENCE' in s;ins.parse(H,['RISneakyAxiom'],O,hostile=True);rec['controls']['custom_axiom']='CAUGHT'
 for n in ['Work','RWInitial','RSBinaryCompare','ForestColorWork']:
  try:run.run(n)
  except AssertionError as e:assert 'REFUSE_DEPENDENCY_REBUILD' in str(e)
  else:raise AssertionError('DEPENDENCY_GUARD_FAILED')
 rec['controls']['dependency_no_rebuild_guard']=4
 deps()
 for e in rec['modules']:pin(R/e['source'],e['source_sha256']);pin(R/e['compiled_source'],e['source_sha256']);pin(R/e['olean'],e['olean_sha256'])
 assert sum(p.stat().st_size for p in O.rglob('*.gz'))<256*1024**2
 rec.update(status='PASS_AUTHOR_REPRESENTED_INITIAL_AND_NORMALIZE_LATER_CONTROL_OPEN',stored_occurrences=len(rows),axiom_union=sorted({a for r in rows for a in r['axiom_references']}),interfaces=required,runtime_direct_references=refs,source_body_close_calls=body_refs,source_body_call_paths=call_witnesses,runtime_decode_encode_or_projection_closure_absent=True,prior_own_closure_occurrences=len(prior),dependency_rebuilds=0,named_positive_checks=20,source_false_diagnoses=12,producer_files=[{'path':str(p.relative_to(R)),'sha256':sha(p)} for p in F.iterdir()],first_gap='Persistent choose (groups/all/filter/unique/mixedCherry) then erase/attempt/step/run and represented receipt/append/counter simulation. Full recovery coefficient remains open.',skipped=['dependency compilation','foreign object-pool merge','independent acceptance','native allocator/compiler/IR and runtime metadata arithmetic correspondence','represented choose/erase/attempt/step/run receipts','global ordinary/forest campaigns','whole recovery bit coefficient and full2.33/base/novelty acceptance'])
 save();print(rec['status'],len(rows),'AX',rec['axiom_union'])
except BaseException as e:rec.update(status='FAIL_RETAINED',error=repr(e));save();raise
