#!/usr/bin/env python3
"""One-shot CB4 guarded-frontier controls; scoring oracle is never generation."""
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from time import perf_counter
import conflict_solver as core
import guarded_frontier as frontier
import exact_conflicts as model

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
started=perf_counter()
controls=[]
for s,t,b,expected in [(None,None,0,0),('a','a',0,0),(['a','b'],['a','b'],0,0),
                        (['a',['b','c']],['b',['a','c']],2,1)]:
    S,T=core.validate_input(s,t,b)
    clean=frontier.guard(S,T,b,0)
    assert clean is not None and clean['original_unmarked_tau_upper_bound']==expected
    assert frontier.verify_certificate(s,t,b,clean)
    controls.append({'source':s,'target':t,'budget':b,'expected_tau_upper_bound':expected,'certificate':clean})
s=[['a','b'],['c','d']];t=[['a','c'],['b','d']]
S,T=core.validate_input(s,t,4)
e=next(e['edge'] for e in S.edge_receipt((1<<len(S.edges))-1) if e['child_labels']==['a','b'])
clean=frontier.guard(S,T,4,1<<e)
assert clean is not None and clean['pure'] and clean['original_unmarked_tau_upper_bound']==0
assert frontier.verify_certificate(s,t,4,clean)
controls.append({'source':s,'target':t,'budget':4,'pure_crossed_pair':True,'certificate':clean})
catches=[]
for key in ['original_labels','full_original_vertices','target_support']:
    bad=deepcopy(clean)
    bad['components'][0][key].append('__bad__' if key=='original_labels' else 999999)
    assert not frontier.verify_certificate(s,t,4,bad)
    catches.append({'kind':key,'caught':True})
bad=deepcopy(clean);bad['components'][0]['local_witness']['cost']+=1
assert not frontier.verify_certificate(s,t,4,bad)
catches.append({'kind':'local-cut-cost','caught':True})
bad=deepcopy(clean);bad['original_source_edge_indices'].append(e)
assert not frontier.verify_certificate(s,t,4,bad)
catches.append({'kind':'duplicate-original-cut','caught':True})
fixtures=json.loads((HERE/'CONTROLS-CB1.json').read_text())['ordinary']
rows=[]
for f in fixtures:
    S,T=core.validate_input(f['source'],f['target'],f['optimum'])
    value,originals,_=model.oracle(S,T)
    assert value==f['optimum']
    cases=[]
    for b in [value,value+2]:
        banned=['oracle','partitions','packing','exact_row']
        saved={name:getattr(model,name) for name in banned}
        def forbidden(*args,**kwargs):
            raise AssertionError('guarded generation used a scoring oracle')
        try:
            for name in banned:setattr(model,name,forbidden)
            generated=frontier.generate(f['source'],f['target'],b)
        finally:
            for name,val in saved.items():setattr(model,name,val)
        certs=generated['certificates']
        assert certs and all(frontier.verify_certificate(f['source'],f['target'],b,c) for c in certs)
        covered=[]
        for c in certs:
            forest=tuple(tuple(d['original_labels']) for d in c['components'])
            covered.append(sum(model.refine(p,forest) for p in originals))
            assert c['precut_cost']<=b and 2*c['original_unmarked_tau_upper_bound']<=b
        assert max(covered)>=1
        cases.append({'budget':b,'outputs':len(certs),'surviving_original_optima_by_output':covered,
                      'generation':generated,'production_oracles_blocked':True})
    rows.append({'id':f['id'],'expected_original_optimum':value,'cases':cases})
assert len(controls)==5 and len(rows)==9
result={'kind':'GLOBAL-CB4-paid-guarded-frontier-controls',
        'date':datetime.now(timezone.utc).isoformat(),
        'verdict':'FINITE-GUARDED-COVER-CONTROLS-PASS; ALPHA-BOUND-OPEN',
        'known_controls_expected':5,'known_controls_executed':len(controls),'controls':controls,
        'ordinary_expected':9,'ordinary_executed':len(rows),'budget_cases':18,'rows':rows,
        'corruptions_caught':len(catches),'corruptions':catches,'seconds':perf_counter()-started,
        'lineage':'same author GLOBAL-C primitives/partition oracle; explicit production ban; not independent certification',
        'scope':'all emitted finite certificates checked for original cuts/terminal geometry/local witnesses/half-budget and existential original-optimum survival; universal graph proof and alpha bound remain open',
        'hashes':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in [HERE/'SPEC-CB4-GUARDED.md',HERE/'guarded_frontier.py',Path(__file__)]}}
dest=ROOT/'research/rmaf/results/algorithm-balanced-cover-continue-cb4-controls.json'
dest.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'receipt':str(dest),'known_controls':len(controls),'ordinary':len(rows),
                  'budget_cases':18,'corruptions_caught':len(catches),'seconds':result['seconds'],
                  'output_counts':[[c['outputs'] for c in r['cases']] for r in rows]}))
