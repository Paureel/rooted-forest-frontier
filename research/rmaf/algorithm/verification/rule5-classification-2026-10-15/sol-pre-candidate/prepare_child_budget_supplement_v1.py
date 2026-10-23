#!/usr/bin/env python3
"""Freeze child-specific refusal/attainment budgets, including the hardest child."""
import hashlib
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
literal={'large8':[1],'sizeTwo7':[1,2,2,2,2],'outside10':[2,3,3,3,4]}
names=['hard-two','p+a','p+b','q+a','q+b']
rows=[]
for case,minima in literal.items():
    for i,minimum in enumerate(minima):
        for remaining,success in [(minimum-1,False),(minimum,True),(minimum+1,True)]:
            rows.append({'case':case,'child':names[i],'paid':2,'remaining':remaining,
                         'rootBudget':remaining+2,'minimumAdditionalCost':minimum,'success':success})
data={'context':'PRE-CANDIDATE supplement from frozen separate cut reference; earlier pins unchanged',
      'literal_child_minima':literal,'queries':rows,
      'zero_child_plant':{'T':[[0,1],2],'ss':[0,1,2],'F':[[0],[1],[2]],'paid':2,
                          'rootBudget':1,'minimumAdditionalCost':0,'expectedCalls':0,
                          'false_truncated_remaining':0,'false_unpaid_success':True},
      'false_twins':['own_minimum_discount','child_minimum_shift','Nat_underflow_unpaid_success']}
p=HERE/'CHILD-BUDGET-SUPPLEMENT-v1.json';assert not p.exists()
p.write_text(json.dumps(data,indent=2)+'\n');p.chmod(0o444)
pin=HERE/'CHILD-BUDGET-SUPPLEMENT-PIN-v1.json'
pin.write_text(json.dumps({'path':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'candidate_contact':False},indent=2)+'\n');pin.chmod(0o444)
print(json.dumps({'frozen_child_queries':len(rows),'includes_outside_q_plus_b_success_at_root_budget':6}))
