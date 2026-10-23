#!/usr/bin/env python3
"""One-shot original-edge denominator receipt for the frozen false B claim."""
import importlib.util,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('own_frozen',HERE/'frozen-readiness-v1/independent_paircase.py')
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
f=json.loads((HERE/'frozen-readiness-v1/preregistration.json').read_text())['fixtures']['T1']
S=m.Original(f['S']);B=frozenset(f['B']);h=S.hull(B);wanted=frozenset([3,4]);rows=[]
for e in S.edges:
    sector=S.descendants(e[1])&B
    rows.append({'original_edge':e,'B_descendant_sector':sorted(sector),'inside_actual_B_embedding':set(e)<=h,
                 'separates_34_from_56':sector==wanted or sector==B-wanted})
assert len(rows)==12 and sum(x['inside_actual_B_embedding'] for x in rows)==6
assert not any(x['separates_34_from_56'] for x in rows)
out={'verdict':'FALSE-WHOLE-B-ONECUT-CLAIM-REJECTED','original_edge_denominator':len(rows),
     'actual_B_embedding_edge_denominator':6,'edges':rows,
     'scope':'Only original whole B false control. Agreed-final-C SourceEdge theorem has different hypotheses.'}
path=HERE.parents[2]/'results/algorithm-pair-case-fresh-review-whole-B-v1.json'
path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ('verdict','original_edge_denominator','actual_B_embedding_edge_denominator')}))
