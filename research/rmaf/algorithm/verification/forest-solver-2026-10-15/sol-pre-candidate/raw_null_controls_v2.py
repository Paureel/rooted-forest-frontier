#!/usr/bin/env python3
"""One-shot exact raw-occurrence/null list bookkeeping prerelease controls."""
from fractions import Fraction
import json
from pathlib import Path
from graph_partition_v2 import mass,raw_gate,equal,expect_caught
HERE=Path(__file__).resolve().parent
spec=json.loads((HERE/'EXPECTATIONS-v6-supplement.json').read_text())
result={'passed':False,'false_twins':[]}
try:
    f=spec['empty_raw_lists']
    equal(str(mass(f['left']+f['right'],Fraction(2))),f['total_mass'],'both zero-output raw lists')
    equal(mass(f['left']+f['right'],Fraction(2))<=Fraction(f['bound_c2']),True,'empty raw mass bound')
    f=spec['zero_output_list']
    equal(str(mass(f['left']+f['right'],Fraction(2))),f['total_mass_c2'],'one empty raw list')
    f=spec['failed_pruned_occurrences']
    raw=f['all']
    equal(str(mass(raw,Fraction(2))),f['total_mass_c2'],'failed/pruned attempts included')
    equal(str(mass(raw[:1],Fraction(2))),f['favorable_only_mass_c2'],'favorable-only lower mass fixture')
    result['false_twins'].append(expect_caught('failed_occurrence_dropped',lambda:raw_gate([raw[0],raw[2]],raw)))
    result['false_twins'].append(expect_caught('pruned_occurrence_dropped',lambda:raw_gate(raw[:2],raw)))
    result['false_twins'].append(expect_caught('all_outputs_filtered_to_favorable',lambda:raw_gate(raw[:1],raw)))
    equal_cost=[{'id':'left','d':1},{'id':'right','d':1}]
    result['false_twins'].append(expect_caught('duplicate_cost_collapsed',lambda:raw_gate(equal_cost[:1],equal_cost)))
    equal(sorted(r['plant'] for r in result['false_twins']),sorted(spec['false_twins']),'raw null detector denominator')
    result['passed']=True
except Exception as exc:
    result['failure']=repr(exc)
    raise
finally:
    (HERE/'raw-null-controls-v2.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'false_twins':len(result['false_twins'])}))
