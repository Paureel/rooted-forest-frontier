"""Finite independent residual verification of every actually emitted B child."""
import json,time
from pathlib import Path
from independent_graph import exact_forest
HERE=Path(__file__).resolve().parent; OUT=HERE.parents[1]/'results'
rows=[]; start=time.perf_counter()
for file in sorted(HERE.glob('paid-reserved-*-stdout.json')):
    ans=json.loads(file.read_text()); raw=json.loads(file.with_name(file.name.replace('-stdout','-input')).read_text()); children=[]
    for s in ans['cover']['states']:
        e=exact_forest(raw['target'],s['source'])
        children.append({'partition':s['partition'],'paid':s['charge'],'exact_residual':e['residual'],'exact_total':s['charge']+e['residual'],'optimal':e['optimal'],'tested':e['tested']})
    rows.append({'input':file.name,'parent_q':ans['additional_cuts'],'children':children,'survival':any(x['exact_total']==ans['additional_cuts'] for x in children),'seconds_from_start':time.perf_counter()-start})
    assert rows[-1]['survival']
    (OUT/'algorithm-review-paid-every-child-progress.json').write_text(json.dumps({'completed':len(rows),'rows':rows},indent=2)+'\n')
assert len(rows)==16
print(json.dumps({'pairs':len(rows),'children':sum(len(x['children']) for x in rows),'seconds':time.perf_counter()-start}))
