"""One-shot continuation orchestration; reuses the calibrated own instruments.
The toolkit index has no Lean stored-declaration inspector; own frozen producer,
row parser, fixed collector and closure walker already cover the needed method.
This adds identity/progress receipts only, not a scientific audit implementation.
"""
import hashlib,json,pathlib,sys,datetime
BASE=pathlib.Path(__file__).resolve().parents[7]
HERE=pathlib.Path(__file__).resolve().parent
OLD=HERE.parent/'postrelease-v1'
def pin(p):
 p=pathlib.Path(p); return {'path':str(p),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def dump(name,data):
 with (HERE/name).open('x') as f:json.dump(data,f,indent=2,sort_keys=True);f.write('\n')
def identity():
 root=json.loads((HERE.parents[1]/'ROOT-RELEASE-v1.json').read_text())
 cp=root['licensed_candidate_packages'][0];mp=BASE/cp['manifest'];assert pin(mp)['sha256']==cp['sha256']
 manifest=json.loads(mp.read_text());n=0
 for row in manifest['immutable_files']:
  p=BASE/row['path'];v=pin(p);assert v['sha256']==row['sha256'] and v['bytes']==row['bytes'],row['path'];n+=1
 plan=json.loads((OLD/'COLD-SOURCE-PLAN-v1.json').read_text());cold=[]
 for name in plan['order']:
  p=OLD/'cold'/(name.replace('.','/')+'.lean');v=pin(p);r=plan['modules'][name]
  assert v['bytes']==r['bytes'] and v['sha256']==r['sha256'],name
  cold.extend([v,pin(p.with_suffix('.olean'))])
 instruments=[]
 for x in ['instrument-v6/Producer.lean','instrument-v6/Producer.olean','instrument-v6/StoredInvoke.lean',
           'instrument-v5/AxiomClosure.lean','instrument-v5/AxiomClosure.olean','bounded_run.py',
           'scan_rows.py','row_audit_frozen.py','row_audit_metadata.py','collect_fixed_audits.py',
           'check_semantics.py','check_closure.py','FIXED-ENV-CALIBRATION-v1.json','CLOSURE-CALIBRATION-v1.json',
           'METADATA-CALIBRATION-v1.json','VISITOR-CALIBRATION-v1.json']:
  p=OLD/x
  if p.exists():instruments.append(pin(p))
 dump('RESUME-IDENTITY-v1.json',{'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
  'candidate_manifest':pin(mp),'matched_candidate_members':n,'cold_sources':425,'cold_artifacts':cold,
  'own_instruments_and_calibration':instruments,'identity_only':True,'new_replication_credit':False})
 print(json.dumps({'candidate_members_matched':n,'cold_sources_matched':len(cold)//2,'own_instrument_pins':len(instruments)}))
if __name__=='__main__':identity()
