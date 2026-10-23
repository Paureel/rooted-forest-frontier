from pathlib import Path
import json,hashlib
import work_ledger as ref
b=Path(__file__).resolve().parent
t=0
for n in range(1,8): t=[t,n]
e=ref.Ledger({'colors':{'kind':'id'}});g=e.literal_current(t);values=e.groups(g)
c={}
for r in e.events:c[r['kind']]=c.get(r['kind'],0)+r['amount']
assert len(values)==8 and c['groups.visit']==15 and c['append.groups.calls']==7 and c['append.groups.left_cells']==28
fine=c['groups.visit']+len(values)+2*c['append.groups.left_cells']+c['append.groups.calls']
assert fine==86
x={'phase':'supplemental post-candidate fine-unit witness, not an extra replication','input_tree':t,'frozen_independent_ledger_sha256':hashlib.sha256((b/'work_ledger.py').read_bytes()).hexdigest(),'counts':c,'singleton_group_cons':len(values),'minimum_distinct_match_and_cons_operations':fine,'candidate_groupsWork_observed_by_clean_Lean_control':79,'difference':fine-79,'events':e.events,'scope':'Refutes only literal helper-as-fine-operation-upper-bound identification; final source cap is much larger and reviewed separately.'}
(b/'SOURCE-UNIT-WITNESS.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:v for k,v in x.items() if k!='events'}))
