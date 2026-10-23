"""One-shot scoped identity freeze; no scientific inference."""
import datetime,hashlib,json,pathlib,signal
signal.alarm(59)
HERE=pathlib.Path(__file__).resolve().parent
PREVIOUS=HERE.parent/'universal_reconstruction_20261016T085144Z/FINAL-MANIFEST-v1.json'
EARLIER=HERE.parent/'resume_20261016T083330Z/FINAL-MANIFEST-v1.json'
def pin(p):
 p=pathlib.Path(p);hh=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):hh.update(chunk)
 return {'path':str(p.resolve()),'bytes':p.stat().st_size,'sha256':hh.hexdigest()}
def verify(row):
 got=pin(row['path']);assert got['bytes']==row['bytes'] and got['sha256']==row['sha256'],row['path']
def main():
 assert pin(PREVIOUS)['sha256']=='3dc130dca4eaf76c51d0834177ad5a4911b30f88ebda4044e0cfd492aaee68bf'
 assert pin(EARLIER)['sha256']=='2cbf35824f2116133ab5f24fb289132cbb2c297fd24ce90de4ed4cc487b34d74'
 old=json.loads(PREVIOUS.read_text());earlier=json.loads(EARLIER.read_text())
 for r in old['files']+earlier['files']:verify(r)
 for name in ['SOURCE-CONTROL-LOCK-v1.json','EVIDENCE-CHECKER-LOCK-v1.json']:
  obj=json.loads((HERE/name).read_text())
  for row in obj.get('files',[obj] if 'path' in obj else []):verify(row)
 ready=json.loads((HERE.parent/'READY-v1.json').read_text())
 for row in ready['installed_runtime_trust_pins']:verify(row)
 cert=json.loads((HERE/'COMMON-DEPENDENCY-CERTIFICATE-v1.json').read_text())
 for row in cert['trusted_runtime_pins']+cert['new_module_pins']+[cert['compiler']]+cert['unchanged_calibrated_producer_pins']:verify(row)
 target=HERE.parents[6]/'research/rmaf/monitoring/next-20261016T092054Z/INDEPENDENT-COMMON-TARGET-v1.json'
 assert pin(target)['sha256']=='ccdd9e68f1c30157a3bc26ce32b32d05e0deee28f70b4485f1421ffe0155632a'
 files=[pin(p) for p in sorted(HERE.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
 verdict=json.loads((HERE/'VERDICT-v1.json').read_text())
 data={'version':1,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
  'status':'IMMUTABLE_COMMON_READY_PRIMITIVE_REUSE_COMMON_LIFT_GEOMETRY_OPEN',
  'no_further_writes_to_listed_phase_files_by_this_review':True,'target':pin(target),
  'previous_manifest':pin(PREVIOUS),'previous_payloads_identity_rechecked':len(old['files']),
  'earlier_manifest':pin(EARLIER),'earlier_payloads_identity_rechecked':len(earlier['files']),
  'new_blind_credit':False,'new_replication_credit':False,
  'verdict':pin(HERE/'VERDICT-v1.json'),'report':pin(HERE/'COMMON-REPORT-v1.md'),
  'proof_certificate':pin(HERE/'COMMON-DEPENDENCY-CERTIFICATE-v1.json'),
  'common_ready':'proved with four explicitly reused structural facts; core contraction independently reconstructed',
  'common_lift':'conditional on unproved expansion and coarsening geometry',
  'conditional_solver_open_parameters':7,'first_open_step':verdict['first_open_step'],
  'next_open_step':verdict['next_open_step'],'full_independent_acceptance':False,
  'prior170_solverlink_dependencies_reused':True,'current225_solverlink_dependencies_reused':True,
  'raw105_partial_qualification_preserved':True,'files':files,'file_count':len(files)}
 p=HERE/'FINAL-MANIFEST-v1.json'
 with p.open('x') as f:json.dump(data,f,indent=2,sort_keys=True);f.write('\n')
 final=pin(p);sha=HERE/'FINAL-MANIFEST-v1.sha256'
 with sha.open('x') as f:f.write(final['sha256']+'  FINAL-MANIFEST-v1.json\n')
 p.chmod(0o444);sha.chmod(0o444)
 print(json.dumps({'status':data['status'],'manifest':final,'members':len(files),'previous_payloads_unchanged':len(old['files'])+len(earlier['files']),'first_gap':verdict['first_open_step']['name']},sort_keys=True))
if __name__=='__main__':main()
