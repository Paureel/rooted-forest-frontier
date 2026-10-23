"""One-shot geometry scope and identity freeze; no source rebuild or solver run."""
import datetime,hashlib,json,pathlib,signal
signal.alarm(59)
HERE=pathlib.Path(__file__).resolve().parent
BASE=HERE.parent
ROOT=HERE.parents[6]
def pin(p):
 p=pathlib.Path(p);h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return {'path':str(p.resolve()),'bytes':p.stat().st_size,'sha256':h.hexdigest()}
def verify(r):
 v=pin(r['path']);assert v['sha256']==r['sha256'],r['path']
 if 'bytes' in r:assert v['bytes']==r['bytes'],r['path']
def pins_in(x):
 if isinstance(x,dict):
  if 'path' in x and 'sha256' in x:verify(x)
  for v in x.values():pins_in(v)
 elif isinstance(x,list):
  for v in x:pins_in(v)
def main():
 prior=[];count=0
 for sub,h in [('resume_20261016T083330Z','2cbf35824f2116133ab5f24fb289132cbb2c297fd24ce90de4ed4cc487b34d74'),('universal_reconstruction_20261016T085144Z','3dc130dca4eaf76c51d0834177ad5a4911b30f88ebda4044e0cfd492aaee68bf'),('common_reconstruction_20261016T092054Z','4613cec0880390a1fe441e578bf5d6e8f82e549dd7d2c0fcc65c3f543e1366bd')]:
  p=BASE/sub/'FINAL-MANIFEST-v1.json';assert pin(p)['sha256']==h
  m=json.loads(p.read_text())
  for r in m['files']:verify(r)
  prior.append({'manifest':pin(p),'payloads_identity_rechecked':len(m['files'])});count+=len(m['files'])
 assert count==1971
 release=BASE.parent/'ROOT-RELEASE-v1.json';assert pin(release)['sha256']=='7b76b8313f55c1425dd900461bf836699ef91f0903582a1e4a7752b6fd7be48a'
 target=ROOT/'research/rmaf/monitoring/common-next-20261016T094138Z/INDEPENDENT-GEOMETRY-TARGET-v1.json'
 assert pin(target)['sha256']=='5cc2cffb371083dd51886efc4c2232d6f70a157bbe0f6d08997644bbf737e797'
 # Verify all phase source/control/checker locks, including refused versions.
 for p in list(HERE.glob('SOURCE-CONTROL-LOCK-v*.json'))+list(HERE.glob('EVIDENCE-CHECKER-LOCK-v*.json')):pins_in(json.loads(p.read_text()))
 cert=json.loads((HERE/'GEOMETRY-DEPENDENCY-CERTIFICATE-v2.json').read_text())
 for r in cert['trusted_runtime_pins']+cert['new_module_pins']+[cert['compiler']]+cert['unchanged_calibrated_producer_pins']:verify(r)
 ready=json.loads((BASE/'READY-v1.json').read_text())
 for r in ready['installed_runtime_trust_pins']:verify(r)
 # Only hashes from the previously frozen own source plan are used; no new census/build.
 plan=json.loads((BASE/'postrelease-v1/COLD-SOURCE-PLAN-v1.json').read_text())
 for mod,r in plan['modules'].items():
  verify({'path':r['source'],'sha256':r['sha256'],'bytes':r['bytes']})
  verify({'path':str(BASE/'postrelease-v1/cold'/(mod+'.lean')),'sha256':r['sha256'],'bytes':r['bytes']})
 assert len(plan['modules'])==425
 verdict=json.loads((HERE/'VERDICT-v1.json').read_text());pins_in(verdict)
 assert cert['common_lift_proved_with_explicit_primitive_reuse'] and cert['expansion_geometry_proved'] and cert['coarsening_geometry_proved']
 assert len(cert['remaining_conditional_parameters'])==6 and not cert['independent_full_solver_exactness']
 assert not cert['partial'] and not cert['unsafe'] and not cert['custom_axioms'] and not cert['forbidden_reached']
 assert cert['body']['rows']==146 and cert['closure_declarations']==3857
 assert set(cert['axioms'])=={'Classical.choice','Quot.sound','propext'}
 trace=json.loads((HERE/'MAY-ASSUME-TRACE-v1.json').read_text());assert trace['actual_count']==118 and trace['conditional_count']==226
 # Every retained process shard is immutable evidence, including refusals.
 for p in (HERE/'evidence').glob('*.json'):
  obj=json.loads(p.read_text())
  for s in obj['shards']:verify({**s,'path':str(HERE/s['path'])})
 files=[pin(p) for p in sorted(HERE.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
 data={'version':1,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
  'status':'IMMUTABLE_COMMON_GEOMETRY_AND_ACTUAL_COMMON_LIFT_WITH_PRIOR_SELECTOR_REUSE',
  'no_further_writes_to_listed_phase_files_by_this_review':True,
  'target':pin(target),'exact_original_release':pin(release),'prior_manifests':prior,
  'prior_payloads_identity_rechecked':count,'original425_sources_and_own_copies_identity_rechecked':425,
  'new_blind_credit':0,'new_replication_credit':0,
  'expansion_geometry_proved':True,'coarsening_geometry_proved':True,'actual_common_lift_proved_with_prior_selector_reuse':True,
  'actual_common_lift_author_dependencies_all_reused':118,'conditional_solver_author_dependencies_all_reused':226,
  'conditional_solver_open_parameters':cert['remaining_conditional_parameters'],'first_open_step':verdict['first_open_step'],
  'full_independent_solver_acceptance':False,'full_runtime_acceptance':False,'native_scope_acceptance':False,'novelty_acceptance':False,
  'raw105_partial_qualification_preserved':True,'intermediate_three_partial_refusal_retained_and_repaired':True,
  'undeclared_simp_dependency_refusals_retained_and_removed_from_final_chain':True,
  'report':pin(HERE/'GEOMETRY-REPORT-v1.md'),'verdict':pin(HERE/'VERDICT-v1.json'),
  'proof_certificate':pin(HERE/'GEOMETRY-DEPENDENCY-CERTIFICATE-v2.json'),'primitive_trace':pin(HERE/'MAY-ASSUME-TRACE-v1.json'),
  'files':files,'file_count':len(files)}
 p=HERE/'FINAL-MANIFEST-v1.json'
 with p.open('x') as f:json.dump(data,f,indent=2,sort_keys=True);f.write('\n')
 final=pin(p);sha=HERE/'FINAL-MANIFEST-v1.sha256'
 with sha.open('x') as f:f.write(final['sha256']+'  FINAL-MANIFEST-v1.json\n')
 p.chmod(0o444);sha.chmod(0o444)
 print(json.dumps({'status':data['status'],'manifest':final,'payloads':len(files),'prior_payloads_unchanged':count,'first_solver_gap':verdict['first_open_step']['name']},sort_keys=True))
if __name__=='__main__':main()
