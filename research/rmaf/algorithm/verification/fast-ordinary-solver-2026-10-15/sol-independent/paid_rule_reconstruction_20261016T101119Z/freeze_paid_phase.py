"""One-shot partial paid reconstruction identity freeze; no solver/build inference."""
import datetime,hashlib,json,pathlib,signal
signal.alarm(59)
HERE=pathlib.Path(__file__).resolve().parent
BASE=HERE.parent;ROOT=HERE.parents[6]
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
 for sub,h in [('resume_20261016T083330Z','2cbf35824f2116133ab5f24fb289132cbb2c297fd24ce90de4ed4cc487b34d74'),('universal_reconstruction_20261016T085144Z','3dc130dca4eaf76c51d0834177ad5a4911b30f88ebda4044e0cfd492aaee68bf'),('common_reconstruction_20261016T092054Z','4613cec0880390a1fe441e578bf5d6e8f82e549dd7d2c0fcc65c3f543e1366bd'),('common_geometry_20261016T094138Z','5c5f0c08f8e16e4cdb309ffcdcbf734f5db77b641cfd2ed0b81bbd4b2788583a')]:
  p=BASE/sub/'FINAL-MANIFEST-v1.json';assert pin(p)['sha256']==h;m=json.loads(p.read_text())
  for r in m['files']:verify(r)
  prior.append({'manifest':pin(p),'payloads_identity_rechecked':len(m['files'])});count+=len(m['files'])
 assert count==2299
 release=BASE.parent/'ROOT-RELEASE-v1.json';assert pin(release)['sha256']=='7b76b8313f55c1425dd900461bf836699ef91f0903582a1e4a7752b6fd7be48a'
 target=ROOT/'research/rmaf/monitoring/independent-next-20261016T101119Z/INDEPENDENT-PAID-RULE-TARGET-v1.json'
 assert pin(target)['sha256']=='ba112efd428c3f4c954b863a3e71e5a7c3477d32ddd0ab66f42bc43c37366ad2'
 for p in list(HERE.glob('SOURCE-CONTROL-LOCK-v*.json'))+list(HERE.glob('EVIDENCE-CHECKER-LOCK-v*.json'))+[HERE/'MAY-ASSUME-v1.json']:pins_in(json.loads(p.read_text()))
 cert=json.loads((HERE/'PAID-DEPENDENCY-CERTIFICATE-v1.json').read_text())
 for r in cert['trusted_runtime_pins']+cert['new_module_pins']+[cert['compiler']]+cert['unchanged_calibrated_producer_pins']:verify(r)
 ready=json.loads((BASE/'READY-v1.json').read_text())
 for r in ready['installed_runtime_trust_pins']:verify(r)
 plan=json.loads((BASE/'postrelease-v1/COLD-SOURCE-PLAN-v1.json').read_text())
 for mod,r in plan['modules'].items():
  verify({'path':r['source'],'sha256':r['sha256'],'bytes':r['bytes']})
  verify({'path':str(BASE/'postrelease-v1/cold'/(mod+'.lean')),'sha256':r['sha256'],'bytes':r['bytes']})
 assert len(plan['modules'])==425
 verdict=json.loads((HERE/'VERDICT-v1.json').read_text());pins_in(verdict)
 assert not cert['one_rule_proved_without_extra_geometry'] and not cert['high_rule_proved_without_extra_geometry']
 assert cert['residual_forest_transfer_open'] and cert['one_pendant_exchange_open'] and cert['high_cherry_forest_dichotomy_open']
 assert not cert['conditional_generic_forest_exactness_reused'] and cert['attempted_author_generic_forest_route_refused']
 assert len(cert['six_original_rule_parameters_remain_open'])==6
 assert not cert['partial'] and not cert['unsafe'] and not cert['custom_axioms'] and not cert['forbidden_reached']
 assert cert['body']['rows']==82 and cert['closure_declarations']==4047
 assert set(cert['axioms'])=={'Classical.choice','Quot.sound','propext'}
 trace=json.loads((HERE/'MAY-ASSUME-TRACE-v3.json').read_text());assert trace['conditional_solver_count']==271 and trace['one_high_count']==241 and trace['prior226_all_retained_reused']
 for p in (HERE/'evidence').glob('*.json'):
  obj=json.loads(p.read_text())
  for s in obj['shards']:verify({**s,'path':str(HERE/s['path'])})
 files=[pin(p) for p in sorted(HERE.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
 data={'version':1,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
  'status':'IMMUTABLE_PAID_CONTROL_PARTIAL_ONE_HIGH_RESIDUAL_TRANSFER_OPEN',
  'no_further_writes_to_listed_phase_files_by_this_review':True,
  'target':pin(target),'exact_original_release':pin(release),'prior_manifests':prior,
  'prior_payloads_identity_rechecked':count,'original425_sources_and_own_copies_identity_rechecked':425,
  'independent_core':['literal best semantics','partition refinement length','paid identity','strict remaining arithmetic','strict callback IH logical adapter','checked caller conditional on explicit coverage/current child contracts'],
  'one_rule_closed':False,'high_rule_closed':False,'residual_forest_transfer_open':True,
  'first_open_step':verdict['first_open_step'],'additional_open_steps':verdict['additional_open_steps'],
  'original_six_rule_parameters_still_open':cert['six_original_rule_parameters_remain_open'],
  'conditional_one_high_author_dependencies_all_reused':241,'conditional_solver_author_dependencies_all_reused':271,
  'prior226_author_dependencies_retained_reused':True,'new_blind_credit':0,'new_replication_credit':0,
  'full_independent_solver_acceptance':False,'full_runtime_acceptance':False,'native_scope_acceptance':False,'novelty_acceptance':False,
  'raw105_partial_qualification_and_all_prior_refusals_preserved':True,'refused_generic_minimum_route_preserved_and_excluded_from_final_chain':True,
  'report':pin(HERE/'PAID-REPORT-v1.md'),'verdict':pin(HERE/'VERDICT-v1.json'),
  'proof_certificate':pin(HERE/'PAID-DEPENDENCY-CERTIFICATE-v1.json'),'primitive_trace':pin(HERE/'MAY-ASSUME-TRACE-v3.json'),
  'files':files,'file_count':len(files)}
 p=HERE/'FINAL-MANIFEST-v1.json'
 with p.open('x') as f:json.dump(data,f,indent=2,sort_keys=True);f.write('\n')
 final=pin(p);sha=HERE/'FINAL-MANIFEST-v1.sha256'
 with sha.open('x') as f:f.write(final['sha256']+'  FINAL-MANIFEST-v1.json\n')
 p.chmod(0o444);sha.chmod(0o444)
 print(json.dumps({'status':data['status'],'manifest':final,'payloads':len(files),'prior_payloads_unchanged':count,'first_gap':verdict['first_open_step']['name']},sort_keys=True))
if __name__=='__main__':main()
