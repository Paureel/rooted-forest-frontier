#!/usr/bin/env python3
"""Check actual/resolved and direct-reference origin attribution, all batches."""
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
receipt=json.loads((HERE/'candidate-origin-batches-v2.json').read_text())
science=set(receipt['expected_producers']);counts={};issues=[];extras=[]
for b in receipt['batches']:
    x=json.loads((HERE/b['path']).read_text());extras.extend(x['extra_names'])
    for r in x['occurrences']:
        if r['resolved_origin'] is None:issues.append({'role':'resolved declaration origin','producer':r['producer'],'name':r['name']})
        for d in r['dependency_producer_map']:
            if d['resolved_origin'] is None:issues.append({'role':'direct dependency origin','producer':r['producer'],'declaration':r['name'],'name':d['name']})
            if not d['stored_producers']:issues.append({'role':'no stored producer candidate','producer':r['producer'],'declaration':r['name'],'name':d['name'],'resolved_origin':d['resolved_origin']})
            counts[d['resolved_origin']]=counts.get(d['resolved_origin'],0)+1
result={'kernel_ConstantInfo_scope':True,'compiled_IR_semantics':'OPEN; not asserted by the kernel occurrence inventory',
        'direct_reference_occurrences':sum(counts.values()),'unattributed_occurrences':issues,
        'direct_reference_origin_counts':counts,'moduleData_extra_const_names':extras,'passed':not issues}
(HERE/'PROVENANCE-SCOPE-CHECK-v1.json').write_text(json.dumps(result,indent=2)+'\n')
assert not issues,'unattributed dependency producer/origin remains'
print(json.dumps({'passed':True,'direct_reference_occurrences':result['direct_reference_occurrences'],
                  'unattributed_occurrences':len(issues),'moduleData_extra_const_names':len(extras)}))
