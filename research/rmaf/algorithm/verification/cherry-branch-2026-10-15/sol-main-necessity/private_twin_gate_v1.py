#!/usr/bin/env python3
"""One-shot additional prerelease same-private-name producer control."""
import hashlib,json,shutil
from pathlib import Path
import origin_gate_v3 as gate
HERE=Path(__file__).resolve().parent; O=HERE/'origin'
records=[]; controls=[]; result={'candidate_contact':False,'commands':records,'controls':controls,'status':'FAIL'}
paths=[O/'private-twin-clean'/'SamePrivate.lean',O/'private-twin-hostile'/'SamePrivate.lean']
pins=json.loads((HERE/'PRIVATE-TWIN-PINS-v1.json').read_text())
for p in paths:
    assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[str(p.relative_to(HERE))]
try:
    combined=O/'private-twin-imports'; combined.mkdir(exist_ok=True)
    for producer,source in [('PrivateCleanTwin',paths[0].parent),('PrivateHostileTwin',paths[1].parent)]:
        build=source/'build'; gate.compile_one('SamePrivate',source,build,'private-twin-'+producer+'-compile',records)
        for artifact in build.glob('SamePrivate.*'):
            shutil.copyfile(artifact,combined/(producer+artifact.name[len('SamePrivate'):]))
    obj=gate.audit(['PrivateCleanTwin'],combined,'private-twin-clean',records)
    gate.gate(obj,['PrivateCleanTwin'],{'PrivateCleanTwin':['Init','Init','Std']})
    controls.append({'control':'private-clean-twin','pass':True,'stored_occurrences':len(obj['rows'])})
    both=gate.audit(['PrivateCleanTwin','PrivateHostileTwin'],combined,'private-twin-both',records)
    shared=[r for r in both['rows'] if r['name'].startswith('_private.') and r['name'].endswith('.BlindPrivateTwin.shared')]
    assert len(shared)==2 and shared[0]['name']==shared[1]['name'] and shared[0]['type']==shared[1]['type']
    assert {r['kind'] for r in shared}=={'axiom','theorem'} and all(r['resolved_kind']=='theorem' for r in shared)
    gate.must_reject('private-unused-coalesced-axiom',lambda:gate.gate(both,['PrivateCleanTwin','PrivateHostileTwin'],{m:['Init','Init','Std'] for m in ['PrivateCleanTwin','PrivateHostileTwin']}),controls)
    result['coalesced_rows']=shared; result['status']='CONTROLS_PASS'
    for p in paths: assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[str(p.relative_to(HERE))]
except Exception as ex:
    result['error']=repr(ex); raise
finally:
    result['seconds']=sum(r['seconds'] for r in records)
    (HERE/'private-twin-run1.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'controls':len(controls),'seconds':result['seconds']}))
