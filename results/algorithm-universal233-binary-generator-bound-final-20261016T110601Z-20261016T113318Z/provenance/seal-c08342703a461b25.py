from pathlib import Path
import collections,gzip,hashlib,json,shutil
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
base=json.loads((D/'ROOT-v1.json').read_text());F=R/json.loads((D/'FINAL-ROOT-v1.json').read_text())['root'];a=json.loads((F/'receipt.json').read_text());V=R/a['replay_root'];rr=json.loads((D/'REPLAY-RESULT-v1.json').read_text());Q=R/rr['root']
assert not (D/'FINAL-MANIFEST-v1.json').exists()
pins={}
licenses=[(R/base['licensed_previous_manifest'],base['licensed_previous_sha256']),
 (R/'research/rmaf/algorithm/universal233/ordinary_dispatch/forest_binary_provider_binding/FINAL-MANIFEST-v1.json','f45ebd68640b1ff514262e4644174c4071d2486390dcd3c36c7982b10be94e5d')]
for path,expected in licenses:
 assert sha(path)==expected
 for row in json.loads(path.read_text())['immutable_files']:
  assert sha(R/row['path'])==row['sha256']
  if row['path'] in pins:assert pins[row['path']]['sha256']==row['sha256']
  pins[row['path']]=row
 pins[str(path.relative_to(R))]={'path':str(path.relative_to(R)),'sha256':expected,'bytes':path.stat().st_size}
for dep in base['dependencies']:
 for f in dep['files']:
  p=R/f['original'];assert sha(p)==f['sha256'];assert p.stat().st_ino==f['original_inode'];assert oct(p.stat().st_mode&0o777)==f['original_mode'];assert sha(R/f['linked'])==f['sha256']
preservation=[]
for n in a['modules']:
 p=D/(n+'.lean');assert sha(p)==sha(F/p.name)
 preservation.append({'path':str(p.relative_to(R)),'sha256':sha(p),'mode':oct(p.stat().st_mode&0o777),'inode':p.stat().st_ino})
checks=[]
for f in a['false_controls']:
 n=f['module'];assert sha(F/(n+'.lean'))==sha(Q/(n+'.lean'));logs=list(Q.glob(n+'-*.log.gz'));assert len(logs)==1
 text=gzip.open(logs[0],'rt').read();assert 'is false' in text or 'omega could not prove' in text
 checks.append({'module':n,'source_sha256':sha(Q/(n+'.lean')),'log_sha256':sha(logs[0]),'result':'EXPECTED_FALSE_REJECTION'})
(Q/'negative-revalidation.json').write_text(json.dumps(checks,indent=2)+'\n')
(F/'source-preservation.json').write_text(json.dumps(preservation,indent=2)+'\n')
num=json.loads((D/'NUMERIC-CONSUMER-BOUNDARY-v1.json').read_text())
for key,hkey in [('manifest','sha256'),('interface','interface_sha256')]:
 p=R/num[key];assert sha(p)==num[hkey];pins[num[key]]={'path':num[key],'sha256':sha(p),'bytes':p.stat().st_size}
for p in D.iterdir():
 if p.is_file():
  q=F/'provenance'/(p.stem+'-'+sha(p)[:16]+p.suffix)
  if q.exists():assert sha(q)==sha(p)
  else:shutil.copyfile(p,q)
for n in ['SCOPE-v1.md','REVIEW-v1.json','JOURNAL-v1.md','finish.py','seal.py','NUMERIC-CONSUMER-BOUNDARY-v1.json','INTERFACE-TRACE-v1.json','FIRST-GAP-v1.json','CONTROL-PLAN-v1.json']:
 q=F/n
 if q.exists():assert sha(q)==sha(D/n)
 else:shutil.copyfile(D/n,q)
assert sha(F/'replay.py')==sha(D/'replay.py')
rows=[]
for b in a['audits']:
 for n in b['producers']:
  with gzip.open(R/b['directory']/(n+'.json.gz'),'rt') as f:rows+=json.load(f)
assert len(rows)==522 and set(x for r in rows for x in r['axiom_references'])=={'Classical.choice','Quot.sound','propext'}
rt=json.loads((F/'runtime-audit.json').read_text())
manifest={
 'version':1,'role':'AUTHOR_LOCAL_COMPLETE_GENERATOR_BOUNDS_AND_ACTUAL_MODULAR_FOREST_RECURSION',
 'status':a['status'],'canonical_receipt':str(F.relative_to(R)),
 'source_replay':str((V/'receipt.json').relative_to(R)),'standalone_replay':str((Q/'receipt.json').relative_to(R)),
 'target':{'path':base['pin'],'sha256':base['pin_sha256']},
 'previous_completed':{'manifest':base['licensed_previous_manifest'],'sha256':base['licensed_previous_sha256']},
 'licensed_provider_audit_manifest':{'manifest':str(licenses[1][0].relative_to(R)),'sha256':licenses[1][1]},
 'numeric_boundary':num,'import_pool':'Only523 exact previous sealed production pairs. Numeric objects not merged. All prior audit records pinned and checked.',
 'source_modules':a['modules'],'production_modules':[x['module'] for x in base['dependencies']]+a['modules'],
 'planted_objects_excluded_from_production':['BoundAuditGhost','BoundBadConversion'],
 'value_roots':{'forest_fixed_point':'GenericForest.BinaryProducer.forestRunBits_value','paid_forest_caller':'GenericForest.BinaryProducer.forestFromInput_value','typed_ordinary_parameter':'Explicit executable ordinary provider plus refinement, not discharged'},
 'cost_roots':['GenericForest.BinaryProducer.overlapProducer_cost','GenericForest.BinaryProducer.Generator.runBits_envelope','GenericForest.BinaryProducer.Generator.generateBits_cost','GenericForest.BinaryProducer.rawProducer_cost','GenericForest.BinaryProducer.branchesProducer_cost','GenericForest.BinaryProducer.generatedRawParent_complete_local'],
 'stored_caps_roots':['GenericForest.BinaryProducer.overlapProducer_caps','GenericForest.BinaryProducer.Generator.generateBits_output','GenericForest.BinaryProducer.branchesProducer_caps'],
 'storage_roots':['GenericForest.BinaryProducer.Generator.generateBits_returned_storage','GenericForest.BinaryProducer.Generator.prefixVolume_bound','GenericForest.BinaryProducer.Generator.generateRetention_bound'],
 'canonicalBinaryGeneratorActual':{
  'actual_raw':'GenericForest.BinaryProducer.rawProducer',
  'complete_local_cost':'GenericForest.BinaryProducer.Generator.generateBits_cost',
  'derived_BranchCaps':'GenericForest.BinaryProducer.branchesProducer_caps',
  'generated_parent':'GenericForest.BinaryProducer.generatedRawParent_complete_local',
  'actual_forest_fixed_point':'GenericForest.BinaryProducer.forestRunBits',
  'paid_forest_caller':'GenericForest.BinaryProducer.forestFromInput',
  'ordinary_provider':'OPEN parameter; missing actual OrdinaryDispatch candidates/cuts/select at FastOrdinary.early',
  'native_heap':'OPEN: prefixVolume is a source reservation/retention ledger, not operational allocator proof'
 },
 'q_dependence':{
  'generator_full_work':'generationCost(W,N,B,C)*2^decode(q); actual colorBits supplies polynomial C at raw source site',
  'raw_branches_full_work':'branchesCost(W,N,B,I,S,P)*2^decode(q)',
  'generated_parent_local':'actual reached callback ledger + generatedParentCost(W,N,B,S,Q)*2^decode(q)',
  'prefix_recurrence':'32*CoreWork.envelope(fuel.length,runCoefficient(W,M)); actual left receipt append and all finite counter updates paid',
  'counter_stored_width':'<=3*fuel.length+4',
  'generated_caps':'m=N*(N+2)+2*N+2; width W, block cells/cuts<=m, blocks<=m+1; indices from actual overlap<=S',
  'returned_storage':'(6*(outputCellCap(W,inputResource(N))+2)+9*N+20)*2^decode(q)',
  'retention':'retentionCost(W,N,B,C)*2^decode(q) for explicit actual-prefix reservation ledger',
  'unproved':'native allocator/GC/stack correspondence; full recursive ordinary/forest work bound and global weighted theorem'
 },
 'callback_boundary':'Forest recursive refinement discharged by actual structural-capacity fixed point; ordinary executable parameter/refinement and returned candidate caps explicit. No supplied whole-cost field.',
 'controls':{'positive_groups':11,'positive_assertions':20,'false_claims_caught':10,'parser_clean':1,'parser_corruptions_caught':5,'forbidden_axiom':'CAUGHT','runtime_decode_injection':'CAUGHT_BY_SAME_RUNTIME_SCAN','earlier_attempts_preserved':True},
 'audit':{'own_producers':18,'own_stored_occurrences':522,'own_kinds':a['audit_kinds'],'prior_exact_records_reused':3021,'full_nonproof_bodies':True,'actual_proof_axiom_walk':True,'axiom_union':a['axiom_union'],'runtime_roots':len(rt['registered']),'runtime_references':len(rt['visited']),'all_custom_runtime_names_resolved':True,'standard_boundary_names':len(rt['standard_boundary']),'runtime_encode_decode_projection_references':0},
 'source_replay_modules':18,'frozen_dependency_rebuilds':0,'independent_credit':0,
 'first_remaining_statement':a['first_remaining'],
 'open':['ordinary actual candidates/cuts/select binding and concrete ordinary recursive handlers','ordinary provider refinement and recursive returned payload/storage contracts','original-input represented conversion, target-leaf capacity inequality and global stored-width/budget-event lineage policy','whole weighted ordinary/optimizer solver theorem2.33','nativeIR/compiler/standard primitive and native allocator/GC/stack operational semantics','fresh independent/base/novelty acceptance'],
 'scope':'SCOPE-v1.md','interfaces':'INTERFACE-TRACE-v1.json','first_gap':'FIRST-GAP-v1.json',
 'immutable_files':[],'self_hash':'FINAL-SEAL-v1.json; manifest and seal excluded recursively.'}

p=R/base['pin'];pins[str(p.relative_to(R))]={'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size}
for root in [F,V,Q]:
 for p in root.rglob('*'):
  if p.is_file() and p.name not in ['manifest.json','FINAL-SEAL-v1.json']:
   pins[str(p.relative_to(R))]={'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size}
manifest['immutable_files']=[pins[k] for k in sorted(pins)]
b=(json.dumps(manifest,indent=2)+'\n').encode();(D/'FINAL-MANIFEST-v1.json').write_bytes(b);(F/'manifest.json').write_bytes(b)
seal={'manifest':str((D/'FINAL-MANIFEST-v1.json').relative_to(R)),'sha256':sha(D/'FINAL-MANIFEST-v1.json'),'immutable_pin_count':len(pins),'canonical_receipt':str(F.relative_to(R)),'status':manifest['status']}
for p in [D/'FINAL-SEAL-v1.json',F/'FINAL-SEAL-v1.json']:p.write_text(json.dumps(seal,indent=2)+'\n');p.chmod(0o444)
(D/'FINAL-MANIFEST-v1.json').chmod(0o444)
for root in [F,V,Q]:
 for p in root.rglob('*'):
  if p.is_file() and not p.is_symlink() and p.stat().st_nlink==1:p.chmod(0o444)
 for p in sorted((p for p in root.rglob('*') if p.is_dir()),key=lambda p:len(p.parts),reverse=True):p.chmod(0o555)
 root.chmod(0o555)
for x in manifest['immutable_files']:assert sha(R/x['path'])==x['sha256']
for row in preservation:
 p=R/row['path'];assert p.stat().st_ino==row['inode'] and oct(p.stat().st_mode&0o777)==row['mode'] and sha(p)==row['sha256']
print(json.dumps(seal),flush=True)
