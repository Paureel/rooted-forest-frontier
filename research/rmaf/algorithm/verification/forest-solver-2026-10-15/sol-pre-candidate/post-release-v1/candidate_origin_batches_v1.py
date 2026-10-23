#!/usr/bin/env python3
"""Bounded producer batches with the unchanged, plant-qualified instrument."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[6]
BUILD=HERE/'isolated-build-v1'
state=json.loads((HERE/'source-rebuild-v1.json').read_text())
assert state['full_passed'] and len(state['runs'])==143
origins=state['independent_topological_order']
(BUILD/'ReviewAll.lean').write_text(''.join('import '+m+'\n' for m in origins))
env={**os.environ,'LEAN_PATH':str(BUILD)}
receipt=HERE/'candidate-origin-batches-v1.json'
result={'commands':[],'batches':[],'expected_producers':origins,'instrument':'producer_audit_v1.lean',
        'instrument_changed_since_qualification':False}
seen=set();producer_seen=set();unique_names=set();resolved_names=set()
all_axioms=set();all_directAX=set();differences=[];total_private=0;direct=[];unresolved=[]


def save():receipt.write_text(json.dumps(result,indent=2)+'\n')


def run(cmd):
    start=time.perf_counter()
    p=subprocess.run(cmd,cwd=BUILD,env=env,text=True,capture_output=True,timeout=60)
    result['commands'].append({'command':cmd,'seconds':time.perf_counter()-start,
        'returncode':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
    save();assert p.returncode==0,'producer batch command failed'


try:
    run([str(ROOT/'bootloops-lean'),'-o','ReviewAll.olean','ReviewAll.lean'])
    for offset in range(0,len(origins),18):
        requested=origins[offset:offset+18]
        out=HERE/('candidate-producer-batch-'+str(offset//18)+'-v1.json')
        run([str(ROOT/'bootloops-lean'),'--run',str(HERE/'producer_audit_v1.lean'),
             'ReviewAll',str(out),*requested])
        data=json.loads(out.read_text())
        rows=data['occurrences'];keys=[(r['producer'],r['ordinal'],r['name']) for r in rows]
        assert len(keys)==len(set(keys))==data['occurrence_count'],'occurrence duplicates/count failure'
        counts={r['producer']:r['stored_count'] for r in data['producer_counts']}
        assert set(counts)==set(requested),'requested producer not stored'
        assert all(sum(r['producer']==n for r in rows)==c for n,c in counts.items()),'stored occurrence dropped'
        assert not(seen & set(keys)),'cross-batch occurrence duplicate'
        seen.update(keys);producer_seen.update(counts)
        for r in rows:
            unique_names.add(r['name'])
            assert r['actual']['name']==r['name'] and r['actual']['origin']==r['producer']
            if r['actual_is_direct_axiom'] or r['actual']['kind']=='axiom':direct.append((r['producer'],r['name']))
            if r['unresolved_dependencies'] or r['resolved'] is None:unresolved.append((r['producer'],r['name'],r['unresolved_dependencies']))
            if r['actual']['kind'] in ['definition','theorem','opaque']:assert r['actual']['body'] is not None
            all_axioms.update(r['actual']['axioms_resolved_name_closure'])
            all_directAX.update(r['directAX_any_stored_producer'])
            total_private+=r['name'].startswith('_private.')
            if not r['actual_equals_resolved_info']:
                differences.append({'producer':r['producer'],'name':r['name'],'resolved_origin':r['resolved_origin'],
                    'kind_same':r['actual']['kind']==r['resolved']['kind'],
                    'type_same':r['actual']['type']==r['resolved']['type'],
                    'body_same':r['actual']['body']==r['resolved']['body']})
        resolved_names.update(r['name'] for r in data['resolved_inventory']['records'])
        result['batches'].append({'path':out.name,'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),
            'json_bytes':out.stat().st_size,'producers':requested,'stored_occurrences':len(rows),
            'resolved_records':data['resolved_inventory']['origin_count']})
        result.update({'stored_occurrences':len(seen),'unique_stored_names':len(unique_names),
            'resolved_scientific_names':len(resolved_names),'producer_modules':len(producer_seen),
            'private_occurrences':total_private,'actual_direct_custom_axioms':direct,
            'unresolved_actual_dependencies':unresolved,'resolved_name_axiom_union':sorted(all_axioms),
            'actual_body_directAX_any_stored_union':sorted(all_directAX),'actual_resolved_info_differences':differences})
        save()
    assert producer_seen==set(origins),'full scientific producer coverage incomplete'
    assert not direct and not unresolved,'custom axiom or unresolved actual dependency'
    assert all_axioms<= {'propext','Classical.choice','Quot.sound'}
    assert all_directAX<= {'propext','Classical.choice','Quot.sound'}
    result['passed']=True;save()
except Exception as exc:
    result['passed']=False;result['failure']=repr(exc);save();raise
print(json.dumps({k:result[k] for k in ['passed','stored_occurrences','unique_stored_names','resolved_scientific_names','producer_modules','private_occurrences']}))
