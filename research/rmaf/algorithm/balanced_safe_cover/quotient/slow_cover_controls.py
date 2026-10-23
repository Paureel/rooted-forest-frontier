#!/usr/bin/env python3
"""Replay controls for the explicitly slow fallback; same-author development."""
from SlowCover import generate_slow,decide_slow,verify_certificate
from quotient_probe import ROOT
import json,time,copy,hashlib
from pathlib import Path
cases=[('singleton','a','a',0,0),
       ('identical',[['a','b'],['c','d']],[['a','b'],['c','d']],0,0),
       ('bad-triple',[['a','c'],'b'],[['a','b'],'c'],1,1),
       ('crossing',[['a','c'],['b','d']],[['a','b'],['c','d']],2,2)]
rows=[];tic=time.perf_counter()
for id,s,t,b,opt in cases:
    certificates=list(generate_slow(s,t,b));best=decide_slow(s,t,b)
    assert certificates and best['total_cost']==opt
    assert all(verify_certificate(s,t,b,c) for c in certificates)
    corrupted=copy.deepcopy(best);corrupted['total_cost']+=1
    assert not verify_certificate(s,t,b,corrupted)
    unique={tuple(sorted(tuple(x['original_labels']) for x in c['components'])) for c in certificates}
    if id=='crossing':assert len(unique)==6
    if id=='bad-triple':assert decide_slow(s,t,0) is None
    rows.append({'id':id,'minimum_paid_cost':best['total_cost'],'expected_optimum':opt,'valid_certificate_realizations':len(certificates),'unique_leaf_partitions':len(unique),'incorrect_accounting_caught':True})
out=ROOT/'results/algorithm-balanced-cover-quotient-slow-controls.json'
out.write_text(json.dumps({'scope':'total slow fallback development; no smaller-base acceptance','rows':rows,'seconds':time.perf_counter()-tic,'source_sha256':hashlib.sha256(Path(__file__).with_name('SlowCover.py').read_bytes()).hexdigest()},indent=2)+'\n')
print(json.dumps({'controls_passed':len(rows),'corruptions_caught':len(rows),'seconds':time.perf_counter()-tic}))
