"""Postcontact mutations against unchanged precontact literal group partition."""
from fresh_graph import *
from pathlib import Path

g=Graph(tree(((0,1),2)))
expected=pkey([{0,1},{2}])
rows=[]
for name,cuts in [('clean_group_cut',[(0,1)]),('missing_group_cut',[]),('cut_inside_group',[(2,3)])]:
    z=g.clone()
    for e in cuts:
        z.cut_original(e)
    accepted=z.partition()==expected
    rows.append({'name':name,'cuts':cuts,'partition':z.partition(),'matches_frozen_expectation':accepted,'pass':accepted==(name=='clean_group_cut')})
result={'scope':'postcontact mutations against unchanged precontact group-cut literal expectation','rows':rows,'passed':sum(r['pass'] for r in rows),'denominator':len(rows)}
p=Path(__file__).parent/'supplementary-group-mutations-v1.json'
p.write_text(json.dumps(jsonable(result),indent=2)+'\n')
print(json.dumps({'passed':result['passed'],'denominator':len(rows)}))
raise SystemExit(0 if all(r['pass'] for r in rows) else 1)
