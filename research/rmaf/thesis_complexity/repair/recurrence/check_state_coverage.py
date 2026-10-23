#!/usr/bin/env python3
"""One-shot adversarial closure checks; no source reachability assertions."""
import json
from fractions import Fraction as F
import check_recurrence as cr
cr.w=lambda p,q:F(3,2)**q/F(2)**p
f=json.loads((cr.HERE/'state-adversary-frozen.json').read_text())
rows=[]
for c in f['controls']:
    r=cr.row(c['id'],*c['parent'],c['children'])
    assert r['pass_mass']==c['expected_mass_pass'] and r['pass_offset']==c['expected_offset_pass']
    rows.append(r)
out={'status':'ARBITRARY-STATE-CLOSURE-REFUTED-NOT-ALGORITHM','metrics':{'controls':len(rows),'arithmetic_obstructions':sum(not(r['pass_mass'] and r['pass_offset']) for r in rows)},'rows':rows,'reachability':f['reachability']}
cr.atomic(cr.RESULT/'thesis-runtime-repair-recurrence-state-coverage.json',out)
print(json.dumps({'status':out['status'],'metrics':out['metrics']},sort_keys=True))
