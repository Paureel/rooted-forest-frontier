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
for n in ['SCOPE-v1.md','REVIEW-v1.json','JOURNAL-v1.md','finish.py','seal.py','NUMERIC-CONSUMER-BOUNDARY-v1.json']:
 q=F/n
 if q.exists():assert sha(q)==sha(D/n)
 else:shutil.copyfile(D/n,q)
assert sha(F/'replay.py')==sha(D/'replay.py')
rows=[]
for b in a['audits']:
 for n in b['producers']:
  with gzip.open(R/b['directory']/(n+'.json.gz'),'rt') as f:rows+=json.load(f)
assert len(rows)==702 and set(x for r in rows for x in r['axiom_references'])=={'Classical.choice','Quot.sound','propext'}
rt=json.loads((F/'runtime-audit.json').read_text())
manifest={'version':1,'role':'AUTHOR_LOCAL_PRODUCER_COSTS_AND_CONCRETE_OVERLAP_RAW_GENERATION','status':a['status'],'canonical_receipt':str(F.relative_to(R)),'source_replay':str((V/'receipt.json').relative_to(R)),'standalone_replay':str((Q/'receipt.json').relative_to(R)),'target':{'path':base['pin'],'sha256':base['pin_sha256']},'previous_completed':{'manifest':base['licensed_previous_manifest'],'sha256':base['licensed_previous_sha256']},'licensed_provider_audit_manifest':{'manifest':str(licenses[1][0].relative_to(R)),'sha256':licenses[1][1]},'numeric_boundary':num,'import_pool':'Only508 exact production pairs from prior producer seal. Numeric object pool not merged. Transitive provider audit records verified separately.','source_modules':a['modules'],'production_modules':[x['module'] for x in base['dependencies']]+a['modules'],'planted_objects_excluded_from_production':['CostsAuditGhost','CostsBadConversion'],'value_roots':{'overlap':'ProducerOverlap.overlapProducer_value','generator':'ProducerGeneratorRun.generateBits_value','actual_raw':'ProducerRawBinding.rawProducer_value','actual_branches':'ProducerRawBinding.branchesProducer_value','generated_raw_parent':'ProducerRawBinding.generatedRawParent_value'},'cost_roots':['ProducerCostAgreement.agreementPair_cost','ProducerCostPretest.pretestBits_cost','ProducerCostJobsSource.jobsBits_cost','ProducerCostJobsSource.sourceForestBits_cost','ProducerCostJobsSource.replaceBits_cost','ProducerCostRawLedger.rawCandidates_ledger','ProducerCostSchedulerLedger.scheduleBits_ledger','ProducerCostAssembly.rawParentProducer_ledger','ProducerCostAssembly.generatedRawParent_ledger'],'q_dependence':{'raw_output_count':'<=6*2^decode(q)','branch_output_count':'<=12*2^decode(q)','materialization':'left.work+right.work+8*left.outputCount+4*right.outputCount+15','generator_full_upper_bound':'OPEN; actual generator work remains an explicit paid term'},'callback_ledger':'Computed sum of actual reached callbacks; no supplied total-cost field. Production recursion and output/storage contracts remain open.','controls':{'positive_groups':12,'positive_assertions':25,'false_claims_caught':8,'parser_clean':1,'parser_corruptions_caught':5,'forbidden_axiom':'CAUGHT','runtime_decode_injection':'CAUGHT_BY_SAME_RUNTIME_SCAN','earlier_attempts_preserved':True},'audit':{'own_producers':15,'own_stored_occurrences':702,'own_kinds':a['audit_kinds'],'prior_exact_records_reused':2319,'full_nonproof_bodies':True,'actual_proof_axiom_walk':True,'axiom_union':a['axiom_union'],'runtime_roots':len(rt['registered']),'runtime_references':len(rt['visited']),'all_custom_runtime_names_resolved':True,'standard_boundary_names':len(rt['standard_boundary']),'runtime_encode_decode_projection_references':0},'source_replay_modules':15,'frozen_dependency_rebuilds':0,'independent_credit':0,'first_remaining_statement':a['first_remaining'],'open':['full overlap/generator traversal, receipt counter/copy and live-storage bounds','generated BranchCaps and recursive payload/storage derivation from inputs','production ordinary/forest recursive implementations and refinement','original-input represented conversion and global fresh-marker stored policy','actual numeric consumer instantiation','weighted whole-solver assembly and theorem2.33','nativeIR/compiler/standard primitive and allocation execution semantics','fresh independent/base/novelty acceptance'],'scope':'SCOPE-v1.md','immutable_files':[],'self_hash':'FINAL-SEAL-v1.json; manifest and seal excluded recursively.'}
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
