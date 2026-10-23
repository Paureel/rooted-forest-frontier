#!/usr/bin/env python3
"""One-shot literal-program replay comparison of the negative scope control."""
import importlib.util
import json
from pathlib import Path
p=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('sol_eval',p/'sol-evaluator-v1.py'); e=importlib.util.module_from_spec(sp); sp.loader.exec_module(e)
f=json.loads((p/'sol-outscope-plant-v1.json').read_text()); s,t=e.Graph(f['S']),e.Graph(f['T'])
_,sec=e.regime(s,t,f['P'],f['edge']); a1,a2,b1,b2=sec; A,B,C=map(set,f['P'])
expected=[]
for name,bs in [('LA',[a1,a2,B,C]),('LB',[A,b1,b2,C])]:
 col={x:i for i,b in enumerate(bs) for x in b}
 expected.extend({'id':f['id']+'/'+name,'q':q,'receipt':e.generate(f['S'],col,q)} for q in range(f['q']+1))
rows=[json.loads(x) for x in (p/'sol-lean/literal-scope-replay.jsonl').read_text().splitlines()]
checks=[a==b for a,b in zip(rows,expected)]
r={'expected_denominator':16,'observed_lean_receipts':len(rows),'observed_python_receipts':len(expected),'exact_equalities':checks,'passed':sum(checks),'all_pass':len(rows)==len(expected)==16 and all(checks)}
(p/'sol-scope-literal-comparison-v1.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
raise SystemExit(0 if r['all_pass'] else 1)
