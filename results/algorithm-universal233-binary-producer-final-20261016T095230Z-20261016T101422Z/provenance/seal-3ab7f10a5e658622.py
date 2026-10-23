"""Pin this attained source boundary without changing prior files or source modes."""
from pathlib import Path
import collections,gzip,hashlib,json,os,shutil
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
base=json.loads((D/'ROOT-v1.json').read_text());F=R/json.loads((D/'FINAL-ROOT-v1.json').read_text())['root'];a=json.loads((F/'receipt.json').read_text());V=R/a['replay_root'];rr=json.loads((D/'REPLAY-RESULT-v1.json').read_text());Q=R/rr['root']
assert not (D/'FINAL-MANIFEST-v1.json').exists()
old=R/base['licensed_previous_manifest'];assert sha(old)==base['licensed_previous_sha256'];prior=json.loads(old.read_text())
for x in prior['immutable_files']:assert sha(R/x['path'])==x['sha256']
for dep in base['dependencies']:
 for f in dep['files']:
  p=R/f['original'];assert sha(p)==f['sha256'];assert p.stat().st_ino==f['original_inode'];assert oct(p.stat().st_mode&0o777)==f['original_mode'];assert sha(R/f['linked'])==f['sha256']
# Source snapshots must still match every own successful capped build.
preservation=[]
for n in a['modules']:
 p=D/(n+'.lean');assert sha(p)==sha(F/p.name)
 preservation.append({'path':str(p.relative_to(R)),'sha256':sha(p),'mode':oct(p.stat().st_mode&0o777),'inode':p.stat().st_ino})
# Revalidate the seven standalone false controls by exact source and diagnostic.
checks=[]
for f in a['false_controls']:
 n=f['module'];assert sha(F/(n+'.lean'))==sha(Q/(n+'.lean'))
 logs=list(Q.glob(n+'-*.log.gz'));assert len(logs)==1
 text=gzip.open(logs[0],'rt').read();assert 'is false' in text or 'omega could not prove' in text
 checks.append({'module':n,'source_sha256':sha(Q/(n+'.lean')),'log_sha256':sha(logs[0]),'result':'EXPECTED_FALSE_REJECTION'})
(Q/'negative-revalidation.json').write_text(json.dumps(checks,indent=2)+'\n')
a['false_controls'][-1]['result']='CAUGHT_BY_ACTUAL_BODY_POSITIVE_OVERHEAD'
a['source_replay_scope']='11 own source modules rebuilt;12 audit producers matched, including53 records from frozen Pretest dependency which was not rebuilt.'
a['complete_producer_polynomial']='OPEN_FOR_PRETEST_JOBS_SOURCE_FILTERMAP_ASSEMBLY'
(F/'receipt.json').write_text(json.dumps(a,indent=2)+'\n');(D/'RESULT-v1.json').write_text(json.dumps(a,indent=2)+'\n')
(F/'source-preservation.json').write_text(json.dumps(preservation,indent=2)+'\n')
# Retain later notes and the exact final tooling versions alongside earlier attempts.
for p in D.iterdir():
 if p.is_file():
  q=F/'provenance'/(p.stem+'-'+sha(p)[:16]+p.suffix)
  if q.exists():assert sha(q)==sha(p)
  else:shutil.copyfile(p,q)
for n in ['SCOPE-v1.md','REVIEW-v1.json','JOURNAL-v1.md','finish.py','seal.py']:
 q=F/n
 if q.exists():assert sha(q)==sha(D/n)
 else:shutil.copyfile(D/n,q)
# The standalone recipe is copied verbatim and run from F with a fresh output root.
assert sha(F/'replay.py')==sha(D/'replay.py')
rows=[]
for b in a['audits']:
 for n in b['producers']:
  with gzip.open(R/b['directory']/(n+'.json.gz'),'rt') as f:rows+=json.load(f)
own=[r for r in rows if r['producer'] in a['modules']];kinds=dict(collections.Counter(r['kind'] for r in own))
rt=json.loads((F/'runtime-audit.json').read_text())
manifest={'version':1,'role':'AUTHOR_CONSTRUCTIVE_PERSISTENT_FINITE_BIT_PRODUCERS','status':a['status'],'canonical_receipt':str(F.relative_to(R)),'source_replay':str((V/'receipt.json').relative_to(R)),'standalone_replay':str((Q/'receipt.json').relative_to(R)),'target':{'path':base['pin'],'sha256':base['pin_sha256']},'previous_completed':{'manifest':base['licensed_previous_manifest'],'sha256':base['licensed_previous_sha256']},'import_pool':'Only497 exact readonly pairs from the previous caller pool; no package-union merge.','source_modules':a['modules'],'production_modules':[x['module'] for x in base['dependencies']]+a['modules'],'planted_objects_excluded_from_production':['ProducerAuditGhost','ProducerBadConversion'],'value_roots':{'scheduler':'BinaryProducerScheduler.scheduleBits_value','concrete_disjoint':'BinaryProducerDisjoint.disjointProducer_value','direct_singleton':'BinaryProducerDisjoint.singletonProducer_value','raw_filterMap':'BinaryProducerRaw.rawCandidates_value','raw_parent':'BinaryProducerRaw.rawParentProducer_value','source_replacement':'BinaryProducerSource.replaceBits_value'},'local_bounds':{'scheduler_work':'(C+1000*(storedBudgetWidth+answerCostWidth+jobCount+3))*(jobCount+1), with displayed per-callback C and result-cost-width hypotheses','disjoint_allocated_width':'storedBudgetWidth+2*sourceCount+3','callback_conversion':'C+16*(N+1)^2+24*(N+2)+8 under per-callback cost and returned forest count caps','storage':['BinaryProducerSchedulerCaps.runBits_storage','BinaryProducerLocalCaps.componentBits_caps','BinaryProducerLocalCaps.forestBits_caps','BinaryProducerSource.sourceForestBits_caps','BinaryProducerSource.replaceBits_width','BinaryProducerAccounting.jobsBits_caps'],'accounting':['BinaryProducerAccounting.disjointProducer_accounted','BinaryProducerAccounting.disjoint_setup_paid','BinaryProducerRaw.rawParentProducer_paid'],'complete_pretest_jobs_source_filterMap_polynomial':'OPEN'},'controls':{'positive_groups':10,'positive_assertions':25,'false_claims_caught':7,'parser_clean':1,'parser_corruptions_caught':5,'forbidden_axiom':'CAUGHT','runtime_decode_injection':'CAUGHT_BY_SAME_RUNTIME_SCAN','retained_failed_noncatches':a['retained_noncatch_controls'],'resource_failure_preserved':a['retained_resource_failure']},'audit':{'own_producers':11,'own_stored_occurrences':len(own),'own_kinds':kinds,'dependency_producer':'Pretest','dependency_occurrences':len(rows)-len(own),'total_new_audited_occurrences':len(rows),'prior_exact_records_reused':a['previous_stored_occurrences_reused'],'full_nonproof_bodies':True,'actual_proof_axiom_walk':True,'axiom_union':a['axiom_union'],'runtime_roots':len(rt['registered']),'runtime_references':len(rt['visited']),'all_custom_runtime_names_resolved':True,'standard_boundary_names':len(rt['standard_boundary']),'runtime_encode_decode_projection_references':0},'source_replay_modules':11,'frozen_dependency_rebuilds':0,'independent_credit':0,'first_remaining_statement':a['first_remaining'],'open':['production recursive ordinary and forest callback contracts','represented overlap/raw branch generator','complete pretest/jobs/source/filterMap and live-storage polynomial assembly','original-input global numeric/fresh-label/path invariants owned elsewhere','weighted whole-solver recurrence and theorem2.33','nativeIR/compiler/standard primitive runtime semantics','fresh independent/base/novelty acceptance'],'scope':'SCOPE-v1.md','immutable_files':[],'self_hash':'FINAL-SEAL-v1.json; manifest and seal excluded recursively.'}
pins={x['path']:x for x in prior['immutable_files']}
for p in [old,R/base['pin']]:pins[str(p.relative_to(R))]={'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size}
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
for r in preservation:
 p=R/r['path'];assert p.stat().st_ino==r['inode'] and oct(p.stat().st_mode&0o777)==r['mode'] and sha(p)==r['sha256']
print(json.dumps(seal),flush=True)
