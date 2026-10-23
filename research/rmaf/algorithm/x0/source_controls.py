"""Supplementary predicate controls; no claim of original preregistration."""
import hashlib
import json
from pathlib import Path
from fresh_oracle import Tree,applicability

here=Path(__file__).resolve().parent
specpath=here/'source-control-spec-v1.json'
spec=json.loads(specpath.read_text())
rows=[]
for case in spec['cases']:
    observed=applicability(Tree(case['T']),Tree(case['Tprime']))
    row=next(r for r in observed['rows'] if r['cherry']==case['cherry'])
    for key,val in case['expected'].items():
        assert row[key]==val,(case['name'],key,row)
    rows.append({'name':case['name'],'expected':case['expected'],'observed':observed,'pass':True})
record={'registration_scope':spec['registration_scope'],'limitation':spec['limitation'],
        'controls':rows,'total':len(rows),'passed':len(rows),
        'source_sha256':hashlib.sha256((here/'fresh_oracle.py').read_bytes()).hexdigest(),
        'spec_sha256':hashlib.sha256(specpath.read_bytes()).hexdigest(),'verdict':'PASS'}
out=here.parents[1]/'results/algorithm-x0-source-controls-v1.json'
out.write_text(json.dumps(record,indent=2)+'\n')
print('PASS supplementary source predicates: 5 / 5')
