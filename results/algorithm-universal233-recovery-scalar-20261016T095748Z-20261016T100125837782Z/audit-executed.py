#!/usr/bin/env python3
"""Owned scalar producer audit; unchanged completed extractor, no dependency build."""
from pathlib import Path
import gzip,importlib.util,json,shutil,sys
sys.dont_write_bytecode=True
import run
D=run.D;R=run.R;O=run.O;sha=run.sha
P=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/forest_check_correspondence';m=json.loads((P/'FINAL-MANIFEST-v1.json').read_text());ip=P/'instrument.py';e=next(x for x in m['immutable_files'] if x['path']==str(ip.relative_to(R)));assert sha(ip)==e['sha256']
spec=importlib.util.spec_from_file_location('completed_scalar_instrument',ip);ins=importlib.util.module_from_spec(spec);spec.loader.exec_module(ins)
mods=['RSBinaryCompare','RSBinaryAdd','RSBinarySubtract','RSBinaryEncoding','RSBinaryCounters','RSBinaryCopy','RSBounds','RSOps','RSOutputs','RSCopy','RSInterface','RSCopyBounds','RSControls']
F=O/'producer-records-v2';F.mkdir();C=O/'AUDIT-CERTIFICATE-v2.json'
rec={'status':'RUNNING_AUTHOR','independent_credit':0,'native_full_recovery_bit_lift':False,'full_algorithm_base_novelty':'ALL_OPEN','modules':[],'controls':{},'runs':[],'instrument':{'path':str(ip.relative_to(R)),'sha256':sha(ip),'unchanged':True}}
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
 pin(O/'RSBounds.lean',sha(D/'RSBounds.lean'))
 try:pin(O/'RSBounds.lean','0'*64)
 except AssertionError as e:assert 'SOURCE_PIN_MISMATCH' in str(e);rec['controls']['changed_hash']='CAUGHT'
 else:raise AssertionError('HASH_COMPARATOR_FAILED')
 for n in mods:
  p=D/(n+'.lean');pin(O/p.name,sha(p));qs=[q for q in O.glob(n+'-*.run.json') if (lambda r:r['exit']==0 and not r['stop_reasons'] and r['source_sha256']==sha(p))(json.loads(q.read_text()))];assert qs,n;q=max(qs,key=lambda p:p.stat().st_mtime_ns)
  rec['modules'].append({'module':n,'source':str(p.relative_to(R)),'source_sha256':sha(p),'compiled_source':str((O/p.name).relative_to(R)),'olean':str((O/(n+'.olean')).relative_to(R)),'olean_sha256':sha(O/(n+'.olean')),'receipt':str(q.relative_to(R)),'receipt_sha256':sha(q)})
 for n,want,count in [('RSControls',0,0),('RSFalseControls',1,12)]:
  p=D/(n+'.lean');qs=[q for q in O.glob(n+'-*.run.json') if (lambda r:r['exit']==want and not r['stop_reasons'] and r['source_sha256']==sha(p))(json.loads(q.read_text()))];assert qs;q=max(qs,key=lambda p:p.stat().st_mtime_ns);r=json.loads(q.read_text());s=gzip.open(R/r['log'],'rt').read();assert s.count('is false')==count
  if n=='RSControls':
   assert '("PASS_RECOVERY_FINITE_CONTROLS", 17, true)' in s
   for c in ['equal','order','minimum','subtract_sat','subtract_two','increment_carry','counter_add','overflow_guard','copy_exact','length','clip','color_head','color_absent','group_copy','tree_copy','output_copy','all_prefixes']:assert s.count('('+json.dumps(c)+', true)')==1,c
  rec['controls'][n]={'receipt':str(q.relative_to(R)),'sha256':sha(q),'false_diagnoses':count}
 (O/'RSAudit.lean').write_text(ins.source(['RSControls'],mods,F));cmd('RSAudit');rows=ins.parse(F,mods,O);names={x['name']:x for x in rows};B='OrdinaryDispatch.RecoveryBits.';S='OrdinaryDispatch.RecoveryScalar.'
 required={S:['fromTree_values','normalize_values','erase_values','group_values','chosen_one_mem','chosen_two_mem','initial_caps','selected_caps','continuation_caps','descendant_caps','descendant_budget','run_events','run_counter_width','scalar_width_inputs','groups_flat_length','groups_flat_values','finish_caps','step_output_caps','run_output_caps','generate_output_caps','output_flatten_cap','checked_color_caps','tree_address_cap','input_resource_polynomial','receipt_field_caps','output_length_width','final_recovery_ranges','source_bound_and_ranges','finite_primitive_work'],B:['compareBits_spec','compareBits_work','equalBits_value','leBits_value','addBits_value','subtractBits_value','scalar_width_bounds','lengthBits_value','lengthBits_work','copyBits_value','copyBits_work','minBits_value','minBits_work','clipBudget_value','clipBudget_work','containsBits_value','containsBits_work','colorBits_value','colorBits_length','colorBits_work','copyArrays_work','copyGroup_value','copyGroup_work','copyTree_value','copyTree_work','copyOutput_value','copyOutput_work','counterAdd_value','counterAdd_work','counterInc_value','counterInc_work','treeCells_source_bound','copyTree_source_bound','forestCells_bound','copyOutput_source_bound']}
 for pre,ns in required.items():
  for n in ns:assert names[pre+n]['kind']=='theorem',pre+n
 runtime=['compareBits','equalBits','leBits','maxBits','addCarry','addBits','incrementBits','subtractBorrow','alignBits','subtractBits','addAtWidth','lengthBits','indexBits','copyBits','copiedEqual','minBits','clipBudget','containsBits','colorBits','copyArrays','copyGroup','copyTree','copyForest','copyOutput','counterAdd','counterInc'];refs={}
 def closure(n,seen):
  if n in seen:return
  seen.add(n)
  row=names.get(n)
  if row is None or row['kind']=='theorem':return
  for x in row['references']:closure(x,seen)
 for n in runtime:
  row=names[B+n];assert row['kind']=='definition' and row['body'] is not None
  seen=set();closure(B+n,seen)
  forbidden=[B+'encode',B+'decode',B+'viewGroup',B+'viewTree',B+'viewOutput','Classical.choose']
  assert not any(x in seen for x in forbidden),(n,seen&set(forbidden));refs[n]=row['references']
 # A range/source conjunction is not a scalar total-work simulation.
 r=names[S+'source_bound_and_ranges'];assert 'OrdinaryDispatch.RecoveryLocalWork.final_source_uniform' in r['references']
 for flavor in ['missing','duplicate']:
  X=O/('producer-'+flavor+'-control-v2');X.mkdir()
  for p in F.iterdir():shutil.copyfile(p,X/p.name)
  if flavor=='missing':
   p=X/'index.json';j=json.loads(p.read_text());j['counts'].pop();p.write_text(json.dumps(j))
  else:
   p=X/'RSBinaryCompare.json.gz';j=json.load(gzip.open(p,'rt'));j.append(j[0]);gzip.open(p,'wt').write(json.dumps(j))
  try:ins.parse(X,mods,O)
  except AssertionError:rec['controls'][flavor+'_producer']='CAUGHT'
  else:raise AssertionError(flavor+'_NOT_CAUGHT')
 (O/'RSSneakyAxiom.lean').write_text('import RSControls\naxiom scalarBad : False\ntheorem scalarBadUse : False := scalarBad\n');cmd('RSSneakyAxiom')
 H=O/'producer-axiom-control-v2';H.mkdir();(O/'RSHostileAudit.lean').write_text(ins.source(['RSSneakyAxiom'],['RSSneakyAxiom'],H));s=cmd('RSHostileAudit',1);assert 'REJECT_PRODUCER_OCCURRENCE' in s;ins.parse(H,['RSSneakyAxiom'],O,hostile=True);rec['controls']['custom_axiom']='CAUGHT'
 for n in ['Work','RWInterface','BinaryCompare','ForestColorWork']:
  try:run.run(n)
  except AssertionError as e:assert 'REFUSE_DEPENDENCY_REBUILD' in str(e)
  else:raise AssertionError('DEPENDENCY_GUARD_FAILED')
 rec['controls']['dependency_no_rebuild_guard']=4
 deps()
 for e in rec['modules']:pin(R/e['source'],e['source_sha256']);pin(R/e['compiled_source'],e['source_sha256']);pin(R/e['olean'],e['olean_sha256'])
 assert sum(p.stat().st_size for p in O.rglob('*.gz'))<256*1024**2
 rec.update(status='PASS_AUTHOR_RECOVERY_RANGES_AND_FINITE_PRIMITIVES_FULL_SIMULATION_OPEN',stored_occurrences=len(rows),axiom_union=sorted({a for r in rows for a in r['axiom_references']}),interfaces=required,runtime_direct_references=refs,runtime_decode_encode_or_projection_closure_absent=True,dependency_rebuilds=0,named_positive_checks=17,source_false_diagnoses=12,producer_files=[{'path':str(p.relative_to(R)),'sha256':sha(p)} for p in F.iterdir()],first_gap='Persistent represented initialization and normalize/choose/erase/run simulation, input conversion and lifetime/receipt materialization ledger. Local bit/copy algorithms are not a full source scalar provider.',skipped=['dependency compilation','binary reference object pool merge','independent acceptance','native/compiler/IR correspondence','full recovery finite-bit bound','global solve/Rule4/Rule5/binary campaigns','full2.33/base/novelty acceptance'])
 save();print(rec['status'],len(rows),'AX',rec['axiom_union'])
except BaseException as e:rec.update(status='FAIL_RETAINED',error=repr(e));save();raise
