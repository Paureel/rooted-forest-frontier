#!/usr/bin/env python3
"""One-shot fresh audit/toy gate runner. All mutations are on in-memory copies.

Expected semantic controls were frozen before the first toy execution. The
pilot's observed origin count is not an expected theorem value and does not
replace the full environment origin-count gate.
"""
from collections import Counter
import copy
import json
import os
from pathlib import Path
import re
import subprocess
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[5]
TOY=HERE/'toy-src'
env={**os.environ,'LEAN_PATH':str(TOY)}
allow={'propext','Classical.choice','Quot.sound'}
result={'commands':[],'gates':[],'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}


def save():
    (HERE/'toy-battery-v2.json').write_text(json.dumps(result,indent=2)+'\n')


def run(label,cmd,expected=0,cwd=TOY):
    start=time.perf_counter()
    local_env={**env,'LEAN_PATH':str(cwd)+os.pathsep+str(TOY)}
    p=subprocess.run(cmd,cwd=cwd,env=local_env,text=True,capture_output=True,timeout=30)
    row={'label':label,'command':cmd,'cwd':str(cwd),'LEAN_PATH':local_env['LEAN_PATH'],'expected_returncode':expected,
         'returncode':p.returncode,'seconds':time.perf_counter()-start,
         'stdout':p.stdout,'stderr':p.stderr}
    result['commands'].append(row)
    save()
    if p.returncode!=expected:
        raise AssertionError('unexpected command returncode: '+label)


def inventory_gate(data, required):
    records=data['records']
    names=[r['name'] for r in records]
    assert len(names)==len(set(names)), 'duplicate origin record'
    assert len(records)==data['origin_count'], 'origin count mismatch'
    assert set(data['requested_origins'])==set(required), 'requested origin set changed'
    counts={r['origin']:r['count'] for r in data['all_module_origin_counts']}
    for origin in required:
        assert origin in data['environment_modules'], 'missing module from environment'
        assert sum(r['origin']==origin for r in records)==counts.get(origin,0), 'missing origin'
    assert all(r['origin'] in required for r in records), 'extraneous origin'
    assert all(r['body'] is not None for r in records if r['kind'] in ['definition','theorem','opaque']), 'missing body'
    bad=set()
    for r in records:
        bad.update(set(r['axioms'])-allow)
        if r['kind']=='axiom':
            bad.add(r['name'])
    assert not bad, 'custom axiom(s): '+repr(sorted(bad))
    return {'origins':len(records),'private':sum(r['name'].startswith('_private.') for r in records),
            'generated':sum(any(tag in r['name'] for tag in ['match_','_f','_sunfold','_unsafe_rec']) for r in records),
            'axioms':sorted({a for r in records for a in r['axioms']})}


def exact_records(data):
    return {r['name']:r for r in data['records']}


def adapter_gate(a,b):
    assert a==b, 'exact type/body/extra/dependency/axiom records differ'


def expect_caught(name,call):
    try:
        call()
    except AssertionError as e:
        result['gates'].append({'name':name,'caught':True,'message':str(e)})
        save()
        return
    raise AssertionError('SURVIVING FALSE TOY: '+name)


try:
    for mod in ['Clean','EmptyDependency','UnusedAxiom','PrivateAxiom']:
        run('compile '+mod,[str(ROOT/'bootloops-lean'),'-o',mod+'.olean',mod+'.lean'])
    run('false theorem compile',[str(ROOT/'bootloops-lean'),'-o','FalseTheorem.olean','FalseTheorem.lean'],1)
    data={}
    for mod,origins in [('Clean',['Clean']),('UnusedAxiom',['Clean','UnusedAxiom']),
                        ('PrivateAxiom',['Clean','PrivateAxiom'])]:
        path=HERE/('toy-'+mod+'-origins-v2.json')
        run('audit '+mod,[str(ROOT/'bootloops-lean'),'--run',str(HERE/'origin_audit_v2.lean'),
                         mod,str(path),*origins])
        data[mod]=json.loads(path.read_text())
    for kind in ['import','body']:
        cwd=HERE/('toy-'+kind+'-adapter-src')
        run('compile same-module '+kind,[str(ROOT/'bootloops-lean'),'-o','Clean.olean','Clean.lean'],cwd=cwd)
        path=HERE/('toy-'+kind+'-same-module-origins-v2.json')
        run('audit same-module '+kind,[str(ROOT/'bootloops-lean'),'--run',str(HERE/'origin_audit_v2.lean'),
            'Clean',str(path),'Clean'],cwd=cwd)
        data[kind]=json.loads(path.read_text())
    clean=inventory_gate(data['Clean'],['Clean'])
    assert clean['private']>0 and clean['generated']>0, 'private/generated origin controls not exercised'
    result['gates'].append({'name':'clean full-origin/private/generated','passed':True,**clean})
    # The theorem queried by a weak auditor does not depend on either axiom.
    for mod,name in [('UnusedAxiom','unused custom axiom'),('PrivateAxiom','private custom axiom')]:
        queried=[r for r in data[mod]['records'] if r['name'].endswith('checkedClean')]
        assert len(queried)==1 and not queried[0]['axioms'], 'unused axiom control contaminated query'
        expect_caught(name,lambda mod=mod:inventory_gate(data[mod],['Clean',mod]))
    missing=copy.deepcopy(data['Clean'])
    missing['records']=missing['records'][1:]
    expect_caught('missing origin',lambda:inventory_gate(missing,['Clean']))
    duplicate=copy.deepcopy(data['Clean'])
    duplicate['records'].append(duplicate['records'][0])
    duplicate['origin_count']+=1
    expect_caught('duplicate origin',lambda:inventory_gate(duplicate,['Clean']))
    # Omission with a forged record count must also fail the separate module tally.
    missing['origin_count']-=1
    expect_caught('missing origin forged total',lambda:inventory_gate(missing,['Clean']))
    public_only=copy.deepcopy(data['Clean'])
    public_only['records']=[r for r in public_only['records'] if not r['name'].startswith('_private.')]
    public_only['origin_count']=len(public_only['records'])
    expect_caught('namespace/public/query-only inventory',lambda:inventory_gate(public_only,['Clean']))
    missing_body=copy.deepcopy(data['Clean'])
    next(r for r in missing_body['records'] if r['kind']=='definition')['body']=None
    expect_caught('missing producer body',lambda:inventory_gate(missing_body,['Clean']))
    baseline=exact_records(data['Clean'])
    imported=exact_records(data['import'])
    adapter_gate(baseline,imported)
    result['gates'].append({'name':'import adapter exact type/body','passed':True,
                            'private_name_only_module_differences':0,'normalization':'NONE'})
    changed=exact_records(data['body'])
    assert baseline['GateToy.publicPayload']['type']==changed['GateToy.publicPayload']['type'], 'body plant changed type'
    expect_caught('body adapter',lambda:adapter_gate(baseline,changed))
    result['gates'].append({'name':'false theorem compilation','caught':True})
    assert len(result['gates'])==11, 'toy denominator mismatch'
    result['passed']=True
    save()
    print(json.dumps({'passed':True,'commands':len(result['commands']),'gates':len(result['gates'])}))
except Exception as exc:
    result['passed']=False
    result['failure']=repr(exc)
    save()
    raise
