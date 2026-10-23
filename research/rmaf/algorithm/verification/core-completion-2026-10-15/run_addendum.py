#!/usr/bin/env python3
"""One-shot extra literal negative witnesses; frozen v1 checker unchanged."""
from datetime import datetime,timezone
import hashlib,importlib,json
from pathlib import Path
from time import perf_counter
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
freeze=json.loads((HERE/'ADDENDUM-FREEZE-v1.json').read_text())
for row in freeze['files']:assert sha(ROOT/row['path'])==row['sha256']
I=importlib.import_module('independent_instrument')
started=perf_counter();rows=[]
for f in json.loads((HERE/'CONTROL-ADDENDUM-v1.json').read_text())['cases']:
 actual=I.validate_emission(f['tree'],{int(k):v for k,v in f['colors'].items()},f['q'],f['output'])
 assert actual==f['expected_valid']
 try:
  assert actual==(not f['expected_valid'])
 except AssertionError:
  caught=True
 else:raise AssertionError('false addendum expectation survived')
 rows.append({'id':f['id'],'valid':actual,'false_expectation_caught':caught,
              'original_residual':I.OriginalGraph(f['tree']).residual(f['output']['cuts'])})
assert len(rows)==4
result={'kind':'core-completion-pre-candidate-explicit-invalid-witness-addendum',
        'stage':'PRE-CANDIDATE','status':'CONTROLS-PASS; NO-CANDIDATE-ACCEPTANCE',
        'date':datetime.now(timezone.utc).isoformat(),'rows':rows,'expected_cases':4,
        'executed_cases':4,'false_expectations_caught':4,'seconds':perf_counter()-started,
        'candidate_contact':False,'candidate_compilation':False,'freeze_sha256':sha(HERE/'ADDENDUM-FREEZE-v1.json')}
p=ROOT/'research/rmaf/results/algorithm-core-completion-fresh-review-prep-addendum-v1.json'
p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'cases':4,'false_expectations_caught':4,'receipt':str(p)}))
