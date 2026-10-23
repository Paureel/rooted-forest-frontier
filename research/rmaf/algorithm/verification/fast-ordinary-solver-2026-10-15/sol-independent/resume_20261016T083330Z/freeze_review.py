"""One-shot immutable identity manifest, no scientific inference."""
import datetime,hashlib,json,pathlib,signal
signal.alarm(59)
HERE=pathlib.Path(__file__).resolve().parent;OLD=HERE.parent/'postrelease-v1'
def pin(p):
 p=pathlib.Path(p);h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
 return {'path':str(p.resolve()),'bytes':p.stat().st_size,'sha256':h.hexdigest()}
def verify(r):
 p=pin(r['path']);assert p['bytes']==r['bytes'] and p['sha256']==r['sha256'],r['path']
def main():
 identity=json.loads((HERE/'RESUME-IDENTITY-v1.json').read_text())
 for r in identity['cold_artifacts']+identity['own_instruments_and_calibration']:verify(r)
 for name in ['CONTINUATION-INSTRUMENT-LOCK-v1.json','EVIDENCE-CHECKER-v2-LOCK.json','USE-SITE-INSTRUMENT-LOCK-v1.json','USE-SITE-INSTRUMENT-LOCK-v2.json']:
  v=json.loads((HERE/name).read_text())
  for r in v.get('files',[v] if 'path' in v else []):verify(r)
 # Preserve the whole owned interrupted-review journal/evidence, including all
 # refusals and failed controls, as provenance rather than fresh execution.
 selected={p for p in OLD.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
 selected.update(p for p in HERE.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
 selected.update([HERE.parent/'READY-v1.json',HERE.parent/'ARTIFACT-LOCK-v1.json'])
 boundary=HERE.parents[1]/'ROOT-RELEASE-v1.json';selected.add(boundary)
 files=[pin(p) for p in sorted(selected)]
 verdict=json.loads((HERE/'VERDICT-v1.json').read_text())
 manifest={'version':1,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
  'status':'IMMUTABLE_SCOPED_NONAUTHOR_REVIEW_COMPLETE_UNIVERSAL_INDEPENDENCE_OPEN',
  'no_further_writes_to_listed_files_by_this_review':True,'new_blind_credit':False,'new_replication_credit':False,
  'candidate_release_sha256':verdict['candidate_release_sha256'],
  'candidate_manifest_sha256':verdict['candidate_manifest_sha256'],
  'verdict':pin(HERE/'VERDICT-v1.json'),'report':pin(HERE/'FUNCTIONAL-REVIEW-v1.md'),
  'first_gap':verdict['first_independent_gap'],
  'preserved_full_raw_cleanliness':'REFUSED: 105 partial declarations',
  'earlier_duplicate_metadata_IR_refusals_preserved':True,
  'pins_revalidated_at_freeze':len(identity['cold_artifacts'])+len(identity['own_instruments_and_calibration']),
  'files':files,'file_count':len(files),'snapshot_meaning':'identity and preserved evidence, not new replication or runtime proof'}
 p=HERE/'FINAL-MANIFEST-v1.json'
 with p.open('x') as f:json.dump(manifest,f,indent=2,sort_keys=True);f.write('\n')
 m=pin(p)
 with (HERE/'FINAL-MANIFEST-v1.sha256').open('x') as f:f.write(m['sha256']+'  FINAL-MANIFEST-v1.json\n')
 # Freeze only newly created resume files. Prior source modes/inodes are untouched.
 for p in HERE.iterdir():
  if p.is_file():p.chmod(0o444)
 print(json.dumps({'status':manifest['status'],'manifest':m,'files':len(files),'prior_owned_files_preserved':True,'first_gap':verdict['first_independent_gap']['statement']},sort_keys=True))
if __name__=='__main__':main()
