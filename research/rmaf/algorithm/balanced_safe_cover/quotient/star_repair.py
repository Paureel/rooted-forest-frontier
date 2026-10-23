#!/usr/bin/env python3
"""Finite constructive repair of the recorded star witness. Development only."""
import json,itertools
from quotient_probe import Tree,tup,ROOT
from geometry_probe import check
f=json.loads((ROOT/'results/algorithm-balanced-cover-quotient-probe.json').read_text())['pilot']
S,T=Tree(tup(f['source'])),Tree(tup(f['target']));b=f['opt'];K=[tuple(e) for e in f['candidate_star_cuts']]
rows=[check(S,T,C,b) for C in itertools.combinations(K,2)]
assert len(rows)==3
for row in rows:
    assert row['pure'] and row['half_budget'] and row['tau']==1
    row['precut_cost']=2
    row['completion_cost']=sum(x['d'] for x in row['local'])
    row['charged_total']=row['precut_cost']+row['completion_cost']
    assert row['charged_total']==b
out=ROOT/'results/algorithm-balanced-cover-quotient-star-repair.json'
out.write_text(json.dumps({'scope':'repair of a single failed proposal; no universal generation claim','rows':rows,'expected_pre_cut_cost':2,'expected_tau':1,'expected_charged_total':3},indent=2)+'\n')
print(json.dumps({'repairs_checked':len(rows),'all_pure':True,'tau':1,'paid_pre_cuts':2,'total':3}))
