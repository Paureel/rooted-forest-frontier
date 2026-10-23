#!/usr/bin/env python3
"""One-shot retained negative scope control; not an in-regime counterexample."""
import importlib.util
import json
from fractions import Fraction
from pathlib import Path
import time
p=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('sol_eval',p/'sol-evaluator-v1.py')
m=importlib.util.module_from_spec(sp); sp.loader.exec_module(m)
f=json.loads((p/'sol-outscope-plant-v1.json').read_text()); start=time.perf_counter()
r=m.analyze_fixture(f,Fraction(233,100))
a=[q['A_contribution']['additional'] for q in r['lists']['LB']['queries']]
split=sum(len(q['A_blocks'])>1 for q in r['lists']['LB']['queries'])
checks={
 'hand_frozen_expectations':all(x['pass'] for x in r['expectation_checks'].values()),
 'scope_guard_catches_corruption':r['guards']['source_P_disjoint']==f['expected_source_P_disjoint'],
 'split_A_residual_costs':a==f['expected_A_post_B_additional_raw_order'],
 'split_A_output_count':split==f['expected_split_A_output_count']}
out={'fixture':r,'checks':checks,'denominator':len(checks),'passed':sum(checks.values()),'seconds':time.perf_counter()-start,'all_pass':all(checks.values())}
(p/'sol-outscope-result-v1.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='fixture'},indent=2))
raise SystemExit(0 if out['all_pass'] else 1)
