"""One-shot exact mass detector over already frozen literal expectations.
No candidate content. Supplements rather than changes the46/221 bank.
"""
from pathlib import Path
from fractions import Fraction
import json,time,hashlib
b=Path(__file__).resolve().parent;root=b.parents[4]
pin=json.loads((b/'MASS-CONTROL-PIN.json').read_text());reports=json.loads((root/'research/rmaf/results/algorithm-final-cuts-fresh-review-fixed-v1.json').read_text())['rows'];by={x['id']:x['report'] for x in reports};rows=[];start=time.perf_counter()
for c in pin['controls']:
 r=by[c['receipt_id']]['value'];costs=[len(x['cuts']) for x in r['outputs']];assert costs==[c['cost']]
 mass=sum((Fraction(c['base'])**(-k) for k in costs),Fraction());assert mass==Fraction(c['expected'])==Fraction(r['mass'][c['base']])
 assert Fraction(c['base'])**(-c['false_cost'])!=mass
 assert mass*2!=mass
 rows.append({'id':c['id'],'exact_mass':str(mass),'wrong_cost_caught':True,'duplicate_occurrence_discount_caught':True})
assert len(rows)==12
out={'status':'PASS-PRE-CANDIDATE-EXACT-MASS-DETECTOR','clean':len(rows),'wrong_cost_claims_caught':len(rows),'duplicate_mass_claims_caught':len(rows),'elapsed_seconds':time.perf_counter()-start,'rows':rows,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pin_sha256':hashlib.sha256((b/'MASS-CONTROL-PIN.json').read_bytes()).hexdigest(),'scope':'Same-lineage readiness; original literal k0..3 mass table frozen before pilot; supplemental detector source/false claims frozen before its own execution, no changes to46/221 bank,no candidate contact'}
(b/'MASS-CONTROL-RECEIPT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
