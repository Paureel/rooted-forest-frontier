#!/usr/bin/env python3
"""One-shot literal-program transcription comparison, not a theorem checker."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import time
p=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('sol_eval',p/'sol-evaluator-v1.py')
e=importlib.util.module_from_spec(spec); spec.loader.exec_module(e)
d=json.loads((p/'sol-fixtures-v1.json').read_text())
rows=[json.loads(x) for x in (p/'sol-lean/literal-replay.jsonl').read_text().splitlines()]
expected=[]
for f in d['fixtures']:
    s,t=e.Graph(f['S']),e.Graph(f['T'])
    guards,sec=e.regime(s,t,f['P'],f['edge']); a1,a2,b1,b2=sec; A,B,C=map(set,f['P'])
    for name,bs in [('LA',[a1,a2,B,C]),('LB',[A,b1,b2,C])]:
        col={x:i for i,b in enumerate(bs) for x in b}
        for q in range(f['q']+1):
            expected.append({'id':f['id']+'/'+name,'q':q,'receipt':e.generate(f['S'],col,q)})
checks=[{'index':i,'id':a['id'],'q':a['q'],'pass':a==b} for i,(a,b) in enumerate(zip(rows,expected))]
corrupt=copy.deepcopy(rows[0]); corrupt['receipt']['outputs'].append({'partition':[[999]],'sourceCuts':['0']})
plant=corrupt!=expected[0]
result={'date_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
        'expected_denominator':82,'observed_lean_receipts':len(rows),'observed_python_receipts':len(expected),
        'full_receipt_equalities':checks,'passed':sum(x['pass'] for x in checks),
        'corrupt_extra_output_caught':plant,
        'lean_receipt_sha256':hashlib.sha256((p/'sol-lean/literal-replay.jsonl').read_bytes()).hexdigest(),
        'all_pass':len(rows)==len(expected)==82 and all(x['pass'] for x in checks) and plant}
(p/'sol-literal-comparison-v1.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='full_receipt_equalities'},indent=2))
raise SystemExit(0 if result['all_pass'] else 1)
