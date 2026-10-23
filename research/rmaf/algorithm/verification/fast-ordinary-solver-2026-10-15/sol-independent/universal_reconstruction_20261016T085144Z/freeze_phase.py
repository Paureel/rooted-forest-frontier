"""One-shot identity freeze of this partial proof phase, no scientific inference."""
import datetime,hashlib,json,pathlib,signal
signal.alarm(59)
HERE=pathlib.Path(__file__).resolve().parent
PREVIOUS=HERE.parent/'resume_20261016T083330Z/FINAL-MANIFEST-v1.json'
def pin(p):
 p=pathlib.Path(p);hh=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):hh.update(chunk)
 return {'path':str(p.resolve()),'bytes':p.stat().st_size,'sha256':hh.hexdigest()}
def verify(row):
 got=pin(row['path']);assert got['bytes']==row['bytes'] and got['sha256']==row['sha256'],row['path']
def main():
 assert pin(PREVIOUS)['sha256']=='2cbf35824f2116133ab5f24fb289132cbb2c297fd24ce90de4ed4cc487b34d74'
 prior=json.loads(PREVIOUS.read_text())
 for r in prior['files']:verify(r)
 for name in ['PROOF-CONTROL-SOURCE-LOCK-v1.json','PROOF-CONTROL-SOURCE-LOCK-v2.json','PROOF-EVIDENCE-CHECKER-LOCK-v1.json','CONTROL-FLOW-EVIDENCE-LOCK-v1.json']:
  obj=json.loads((HERE/name).read_text())
  for row in obj.get('files',[obj] if 'path' in obj else []):verify(row)
 ready=json.loads((HERE.parent/'READY-v1.json').read_text())
 for row in ready['installed_runtime_trust_pins']:verify(row)
 certificates=[]
 for name in ['PROOF-DEPENDENCY-CERTIFICATE-v1.json','CONTROL-FLOW-DEPENDENCY-CERTIFICATE-v1.json']:
  d=json.loads((HERE/name).read_text())
  for row in d['trusted_runtime_pins']+[d['new_source'],d['new_olean'],d['compiler']]+d['unchanged_calibrated_producer_pins']:verify(row)
  certificates.append(pin(HERE/name))
 target=HERE.parents[6]/'research/rmaf/monitoring/next-20261016T085144Z/UNIVERSAL-RECONSTRUCTION-TARGET-v1.json'
 assert pin(target)['sha256']=='5c82a0912b2522ff8eb7ccc389dac1682c43191618ec963ef2466863253dbba3'
 selected={p for p in HERE.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
 files=[pin(p) for p in sorted(selected)]
 verdict=json.loads((HERE/'VERDICT-v1.json').read_text())
 data={'version':1,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
  'status':'IMMUTABLE_SUBSTANTIVE_PARTIAL_RECONSTRUCTION_FULL_TARGET_OPEN',
  'no_further_writes_to_listed_phase_files_by_this_review':True,
  'new_blind_credit':False,'new_replication_credit':False,'target':pin(target),
  'previous_frozen_manifest':pin(PREVIOUS),'previous_members_identity_rechecked':len(prior['files']),
  'original_runtime_pins_matched':len(ready['installed_runtime_trust_pins']),
  'verdict':pin(HERE/'VERDICT-v1.json'),'report':pin(HERE/'RECONSTRUCTION-REPORT-v1.md'),
  'proof_certificates':certificates,'first_open_step':verdict['first_open_step'],
  'independent_part':'successful pretest minimum/query; global solver linkage preserves typed definition reuse',
  'conditional_induction_rule_parameters_uninstantiated':8,
  'full_independent_solver_acceptance':False,'prior_105_partial_refusal_preserved':True,
  'new_solver_oracle_evaluator_runs':0,'new_cold_builds':0,'new_old_raw_audits':0,'new_finite_censuses':0,
  'files':files,'file_count':len(files)}
 p=HERE/'FINAL-MANIFEST-v1.json'
 with p.open('x') as f:json.dump(data,f,indent=2,sort_keys=True);f.write('\n')
 final=pin(p)
 sha=HERE/'FINAL-MANIFEST-v1.sha256'
 with sha.open('x') as f:f.write(final['sha256']+'  FINAL-MANIFEST-v1.json\n')
 # Only the just-created manifest and detached hash change mode. Previously
 # frozen controls, failure files, original sources and old snapshots are untouched.
 p.chmod(0o444);sha.chmod(0o444)
 print(json.dumps({'status':data['status'],'manifest':final,'members':len(files),'previous1860members_unchanged':True,'first_open_step':verdict['first_open_step']['name']},sort_keys=True))
if __name__=='__main__':main()
