from fractions import Fraction
from pathlib import Path
import json,hashlib,time
root=Path(__file__).resolve().parents[5];b=Path(__file__).resolve().parent;pin=b/'MASS-CONTROL-PIN-v1.json';p=json.loads(pin.read_text());r=root/'research/rmaf/results/algorithm-query-classifier-fresh-review-controls-v2.json';rows=json.loads(r.read_text())['rows'];clean=bad=0;out=[];t=time.perf_counter()
for f in p['fixtures']:
 observed=next(x['report']['value']['costs'] for x in rows if x['id']==f['receipt_id']);assert observed==f['costs']
 for c,expected in f['mass'].items():
  base=Fraction(c);mass=lambda xs:sum((base**(-x) for x in xs),Fraction(0));assert str(mass(observed))==expected;clean+=1
  for false in f['false_cost_lists']:assert str(mass(false))!=expected;bad+=1
  out.append({'fixture':f['id'],'base':c,'exact_mass':expected})
sole=next(x['report']['value'] for x in rows if x['id']=='sole-hard-budget5-no-discount')
for c,false in zip(['2','233/100','3'],p['false_query_discount_claims']):assert sole['mass'][c]['exact']==p['sole_hard_query_mass'] and sole['mass'][c]['exact']!=false;bad+=1
x={'status':'PASS-PRERELEASE-EXACT-MASS-CONTROLS','literal_source_mass_cases':clean,'false_mass_or_discount_claims_caught':bad,'seconds':time.perf_counter()-t,'source_mass_values':out,'pin_sha256':hashlib.sha256(pin.read_bytes()).hexdigest(),'instrument_receipt_sha256':hashlib.sha256(r.read_bytes()).hexdigest(),'candidate_contact':False,'independent_replications_added':0}
(b/'MASS-CONTROL-RECEIPT.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x))
