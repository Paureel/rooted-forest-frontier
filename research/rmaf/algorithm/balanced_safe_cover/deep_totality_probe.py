#!/usr/bin/env python3
"""One-shot implementation totality probe; no optimization oracle used.
Identical trees have optimum0 by construction. Tests the actual fallback entry.
"""
import hashlib, importlib, json, pathlib, sys, time
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[3]
sys.path.insert(0,str(HERE/'quotient'))
slow=importlib.import_module('SlowCover')
fixture=HERE/'IMPLEMENTATION-CONTROLS.json'
controls=json.loads(fixture.read_text())
rows=[]
for case in controls['fixtures']:
    tree='a0'
    for i in range(1,case['depth']+1):tree=(f'a{i}',tree)
    started=time.monotonic()
    try:
        outputs=list(slow.generate_slow(tree,tree,case['budget']))
        actual={'outputs':len(outputs),'total_cost':outputs[0]['total_cost'] if outputs else None,'exception':None}
    except Exception as error:
        actual={'outputs':None,'total_cost':None,'exception':type(error).__name__,'message':str(error)}
    row={'id':case['id'],'depth':case['depth'],'leaves':case['leaves'],'actual':actual,
         'expected':{k:case['expected_'+k] for k in ('outputs','total_cost','exception')},
         'seconds':time.monotonic()-started}
    row['passed']=all(actual[k]==v for k,v in row['expected'].items())
    rows.append(row)
assert rows[0]['passed'],'clean twin must pass before interpreting deep failure'
corruption_caught=rows[0]['actual']['outputs']!=0
assert corruption_caught,'known output-count corruption survived'
result={'kind':'actual-fallback-totality-control','rows':rows,'expected_count':2,'executed_count':len(rows),
        'comparator_corruption_caught':corruption_caught,
        'status':'passed' if all(r['passed'] for r in rows) else 'EXACT-IMPLEMENTATION-TOTALITY-FAILURE',
        'scope':controls['scope'],'recursion_limit':sys.getrecursionlimit(),
        'fixture_sha256':hashlib.sha256(fixture.read_bytes()).hexdigest(),
        'slow_source_sha256':hashlib.sha256(pathlib.Path(slow.__file__).read_bytes()).hexdigest(),
        'script_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
output=ROOT/'research/rmaf/results/algorithm-balanced-cover-deep-totality.json'
output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'rows':[{k:r[k] for k in ('id','actual','passed','seconds')} for r in rows],
                  'receipt':str(output)}))
