import pathlib,json,hashlib,datetime
HERE=pathlib.Path(__file__).resolve().parent
BASE=HERE.parent
ROOT=HERE.parents[6]
def digest(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def verify(row):
 p=pathlib.Path(row['path']);assert p.is_file(),str(p)
 assert p.stat().st_size==row['bytes'] and digest(p)==row['sha256'],str(p)
prior=[('resume_20261016T083330Z','2cbf35824f2116133ab5f24fb289132cbb2c297fd24ce90de4ed4cc487b34d74',1860),('universal_reconstruction_20261016T085144Z','3dc130dca4eaf76c51d0834177ad5a4911b30f88ebda4044e0cfd492aaee68bf',62),('common_reconstruction_20261016T092054Z','4613cec0880390a1fe441e578bf5d6e8f82e549dd7d2c0fcc65c3f543e1366bd',49),('common_geometry_20261016T094138Z','5c5f0c08f8e16e4cdb309ffcdcbf734f5db77b641cfd2ed0b81bbd4b2788583a',328),('paid_rule_reconstruction_20261016T101119Z','7806073337c21cc0f0f5f901279e794d76c559f4ec6611c417d410b876d4ddd3',114),('one_exchange_20261016T103152Z','64f52d38d54f52bce134997a6ca4144370ca595e04a44825226a286b009a359f',81)]
checked=[]
for directory,sha,count in prior:
 p=BASE/directory/'FINAL-MANIFEST-v1.json';assert digest(p)==sha
 data=json.loads(p.read_text());assert len(data['files'])==count
 for row in data['files']:verify(row)
 checked.append({'path':str(p),'sha256':sha,'verified_payloads':count})
plan=json.loads((BASE/'postrelease-v1/COLD-SOURCE-PLAN-v1.json').read_text())
assert len(plan['modules'])==425
for module,row in plan['modules'].items():
 p=pathlib.Path(row['source']);cold=BASE/'postrelease-v1/cold'/(module+'.lean')
 assert p.stat().st_size==row['bytes'] and digest(p)==row['sha256']
 assert cold.stat().st_size==row['bytes'] and digest(cold)==row['sha256']
release=BASE.parent/'ROOT-RELEASE-v1.json';assert digest(release)=='7b76b8313f55c1425dd900461bf836699ef91f0903582a1e4a7752b6fd7be48a'
ready=BASE/'READY-v1.json';assert digest(ready)=='9cfaa653f84caf2bae44bdefa4b976500c10c69c7095cb99b5401becaaa55dc1'
r=json.loads(ready.read_text());runtime=r['installed_runtime_trust_pins']
for row in runtime:verify(row)
for row in r['owned_files']:verify(row)
target=ROOT/'research/rmaf/monitoring/one-next-20261016T105900Z/ONE-CLADE-SPLIT-TARGET-v1.json'
assert digest(target)=='8676944dd51965e8a2601107d3072c7fd360b42efd1845839a55d31664cf2a70'
cert=json.loads((HERE/'CLADE-SPLIT-DEPENDENCY-CERTIFICATE-v1.json').read_text())
for row in cert['trusted_runtime_pins']+cert['unchanged_calibrated_producer_pins']+cert['new_module_pins']:verify(row)
result={'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'prior_manifests':checked,'unchanged_payloads':sum(x['verified_payloads'] for x in checked),'original_author_sources_and_own_cold_copies_matched':425,'ready_own_files_matched':len(r['owned_files']),'ready_runtime_pins_matched':len(runtime),'current_actual_runtime_pins_matched':len(cert['trusted_runtime_pins']),'old_calibrated_producer_pins_matched':len(cert['unchanged_calibrated_producer_pins']),'source_olean_pins_matched':len(cert['new_module_pins']),'release_sha256':digest(release),'target_sha256':digest(target),'hash_only_preservation_check':True,'no_new_raw_author_audit_or_build':True,'preserved_qualifications':['Raw original105 partial declarations','Geometry3 partial recursive helper refusals and implicit simp refusals','Paid generic forest exactness route reaches forbidden globalminimum and remains refused','All prior failed compiles and false/corrupt controls']}
p=HERE/'PRIOR-PRESERVATION-v1.json'
with p.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(result,sort_keys=True))
