#!/usr/bin/env python3
"""Compile pinned original import-only counterparts with fresh dependency aliases.

Only 14 sources change imports; the other 129 are byte-identical originals.
Every alias is compiled from a pinned adapted dependency source; no scientific
olean is copied. Source and all type/body differences remain explicit.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[6];BUILD=HERE/'isolated-build-v1'
source_state=json.loads((HERE/'source-rebuild-v1.json').read_text())
catalog={r['module']:r for r in source_state['source_records']}
changed=[r['module'] for r in source_state['source_records'] if r['adaptations']]
assert len(changed)==14 and all(r['original_reconstructed_exactly'] for r in catalog.values())
mode=sys.argv[1];wanted=changed[:1] if mode=='pilot' else changed
receipt=HERE/'original-adapter-review-v1.json'
result=json.loads(receipt.read_text()) if receipt.exists() else {'commands':[],'modules':[],
    'unchanged_source_modules':[n for n,r in catalog.items() if not r['adaptations']],
    'context':'post-contact exact source/type/body comparison; no normalization'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()


def save():receipt.write_text(json.dumps(result,indent=2)+'\n')


def run(cmd,cwd,path):
    started=time.perf_counter();env={**os.environ,'LEAN_PATH':path}
    p=subprocess.run(cmd,cwd=cwd,env=env,text=True,capture_output=True,timeout=30)
    result['commands'].append({'command':cmd,'cwd':str(cwd),'LEAN_PATH':path,'returncode':p.returncode,
                              'seconds':time.perf_counter()-started,'stdout':p.stdout,'stderr':p.stderr})
    save();assert p.returncode==0,'original adapter command failed'


try:
    done={r['module'] for r in result['modules']}
    for n in wanted:
        if n in done:continue
        row=catalog[n];folder=HERE/'original-contexts-v1'/n;folder.mkdir(parents=True,exist_ok=False)
        original=HERE/'reconstructed-original-source-v1'/(n+'.lean')
        assert sha(original)==row['sha256']
        (folder/(n+'.lean')).write_bytes(original.read_bytes())
        aliases=[]
        for old,new in row['adaptations'].items():
            src=BUILD/(new+'.lean');assert sha(src)==catalog[new]['adapted_sha256']
            (folder/(old+'.lean')).write_bytes(src.read_bytes())
            run([str(ROOT/'bootloops-lean'),'-o',old+'.olean',old+'.lean'],folder,str(BUILD))
            aliases.append({'original_import':old,'pinned_dependency_module':new,'source_sha256':sha(src),
                            'fresh_alias_olean_sha256':sha(folder/(old+'.olean'))})
        run([str(ROOT/'bootloops-lean'),'-o',n+'.olean',n+'.lean'],folder,str(folder)+os.pathsep+str(BUILD))
        paths={}
        for label,cwd,path in [('original',folder,str(folder)+os.pathsep+str(BUILD)),('adapted',BUILD,str(BUILD))]:
            out=HERE/('original-adapter-'+n+'-'+label+'-v1.json');paths[label]=out
            run([str(ROOT/'bootloops-lean'),'--run',str(HERE/'producer_audit_v4.lean'),n,str(out),n],cwd,path)
        data={k:json.loads(p.read_text()) for k,p in paths.items()}
        records={k:{r['name']:r for r in x['occurrences']} for k,x in data.items()}
        assert len(records['original'])==data['original']['occurrence_count']
        assert len(records['adapted'])==data['adapted']['occurrence_count']
        assert set(records['original'])==set(records['adapted']),'original/adapted declaration-name set drift'
        differences=[]
        exact_fields=['kind','type','body','extra','dependencies','universe_parameters','unsafe','partial']
        for name in records['original']:
            a=records['original'][name];b=records['adapted'][name]
            assert not a['actual_is_direct_axiom'] and not b['actual_is_direct_axiom']
            assert not a['unresolved_dependencies'] and not b['unresolved_dependencies']
            changed_fields=[k for k in exact_fields if a['actual'][k]!=b['actual'][k]]
            if a['directAX_any_stored_producer']!=b['directAX_any_stored_producer']:changed_fields.append('directAX_any_stored_producer')
            if changed_fields:differences.append({'name':name,'fields':changed_fields})
        result['modules'].append({'module':n,'original_sha256':row['sha256'],'adapted_sha256':row['adapted_sha256'],
            'aliases':aliases,'stored_occurrences':len(records['original']),'type_body_directAX_exact':not differences,
            'differences':differences,'records':{k:{'path':p.name,'sha256':sha(p)} for k,p in paths.items()}})
        save()
    result[mode+'_complete']=True
    result['all_completed_type_body_exact']=all(r['type_body_directAX_exact'] for r in result['modules'])
    save()
except Exception as exc:
    result['failure']=repr(exc);save();raise
print(json.dumps({'mode':mode,'compared_import_adapters':len(result['modules']),
                  'all_completed_type_body_exact':result['all_completed_type_body_exact']}))
