#!/usr/bin/env python3
"""One-shot additional local forest control; not a root-reachability witness."""
import json
from pathlib import Path
from check import parse,label,mark,normal,child,freeze,mass,protected
f1=parse('((a,((x,y),(u,v))),((p,q),(r,(b,(s,t)))))')
f2=[parse('(((x,p),q),(y,r))'),parse('((u,s),(v,t))').kids[0],parse('(a,b)').kids[0]]
mark([f1],[label('a')]);mark(f2,[label('a'),label('b')])
trace=[]
for selected,expected in [('x,y','A3BC'),('u,v','A2BC')]:
    f1,f2,r=normal(f1,f2,tuple(map(label,selected.split(','))))
    assert r['case']==expected and all(x['legal'] for x in r['branches'])
    trace.append({'F1':f1.text(),'F2':[x.text() for x in f2],'rule':freeze(r),'protected_F1':protected([f1]),'protected_F2':protected(f2)})
    f1,f2=child(f1,f2,next(x for x in r['branches'] if x['name']=='C'))
f1,f2,r=normal(f1,f2)
assert set(r['pair'])=={label('x'),label('u')}
assert r['case']=='AC' and not any(x['legal'] for x in r['branches'])
trace.append({'F1':f1.text(),'F2':[x.text() for x in f2],'rule':freeze(r),'protected_F1':protected([f1]),'protected_F2':protected(f2)})
result={'status':'PASS','scope':'locally admissible disconnected three-protected endpoint state; not claimed reachable from original unprotected trees','expected_end_case':'AC','legal_end_branches':0,'trace':trace}
p=Path('research/rmaf/results/thesis-runtime-repair-geometry-disconnected.json');tmp=p.with_suffix('.tmp');tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(p)
print(json.dumps({k:v for k,v in result.items() if k!='trace'}))
