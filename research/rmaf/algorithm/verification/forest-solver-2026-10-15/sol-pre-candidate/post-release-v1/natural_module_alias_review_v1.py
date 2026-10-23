#!/usr/bin/env python3
"""Explicit original-basename versus canonical-module counterpart inventory."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[6];BUILD=HERE/'isolated-build-v1'
state=json.loads((HERE/'source-rebuild-v1.json').read_text());catalog={r['module']:r for r in state['source_records']}
wanted=[r for r in state['source_records'] if Path(r['path']).stem!=r['module']]
assert len(wanted)==15
result={'context':'post-contact original-basename comparison; raw records retained','commands':[],'modules':[]}
receipt=HERE/'natural-module-alias-review-v1.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()


def save():receipt.write_text(json.dumps(result,indent=2)+'\n')


def rename(s,mapping):
    for old,new in mapping.items():
        marker=re.compile(r'(_private\.|«_@»\.)'+re.escape(old)+r'(?=\.|\s|$)')
        if marker.search(s):s=marker.sub(lambda m:m.group(1)+new,s).replace('"'+old+'"','"'+new+'"')
    return s


def norm(x,mapping):
    if isinstance(x,str):return rename(x,mapping)
    if isinstance(x,list):return [norm(v,mapping) for v in x]
    if isinstance(x,dict):return {k:norm(v,mapping) for k,v in x.items()}
    return x


def run(cmd,cwd,path):
    start=time.perf_counter();p=subprocess.run(cmd,cwd=cwd,env={**os.environ,'LEAN_PATH':path},text=True,capture_output=True,timeout=30)
    result['commands'].append({'command':cmd,'cwd':str(cwd),'LEAN_PATH':path,'returncode':p.returncode,
                              'seconds':time.perf_counter()-start,'stdout':p.stdout,'stderr':p.stderr})
    save();assert p.returncode==0,'natural-root counterpart command failed'


try:
    for row in wanted:
        canonical=row['module'];original_name=Path(row['path']).stem
        folder=HERE/'natural-original-contexts-v1'/canonical;folder.mkdir(parents=True,exist_ok=False)
        src=HERE/'reconstructed-original-source-v1'/(canonical+'.lean');assert sha(src)==row['sha256']
        (folder/(original_name+'.lean')).write_bytes(src.read_bytes())
        aliases=[]
        for old,new in row['adaptations'].items():
            dep=BUILD/(new+'.lean');assert sha(dep)==catalog[new]['adapted_sha256']
            (folder/(old+'.lean')).write_bytes(dep.read_bytes())
            run([str(ROOT/'bootloops-lean'),'-o',old+'.olean',old+'.lean'],folder,str(BUILD))
            aliases.append({'original_import':old,'pinned_dependency_module':new,'source_sha256':sha(dep)})
        run([str(ROOT/'bootloops-lean'),'-o',original_name+'.olean',original_name+'.lean'],folder,str(folder)+os.pathsep+str(BUILD))
        data={};paths={}
        for label,module,cwd,path in [('original',original_name,folder,str(folder)+os.pathsep+str(BUILD)),
                                      ('canonical',canonical,BUILD,str(BUILD))]:
            out=HERE/('natural-alias-'+canonical+'-'+label+'-v1.json');paths[label]=out
            run([str(ROOT/'bootloops-lean'),'--run',str(HERE/'producer_audit_v4.lean'),module,str(out),module],cwd,path)
            data[label]=json.loads(out.read_text())
        mapping={original_name:canonical,**row['adaptations']}
        original={rename(r['name'],mapping):r for r in data['original']['occurrences']}
        canonical_records={r['name']:r for r in data['canonical']['occurrences']}
        assert len(original)==data['original']['occurrence_count']
        assert len(canonical_records)==data['canonical']['occurrence_count']
        assert set(original)==set(canonical_records),'non-Name original-root declaration-set difference'
        changes=[];unresolved=[]
        fields=['kind','type','body','extra','universe_parameters','unsafe','partial']
        for name,a in original.items():
            b=canonical_records[name]
            assert not a['actual_is_direct_axiom'] and not b['actual_is_direct_axiom']
            assert not a['unresolved_dependencies'] and not b['unresolved_dependencies']
            raw=[k for k in fields if a['actual'][k]!=b['actual'][k]]
            remaining=[k for k in raw if norm(a['actual'][k],mapping)!=b['actual'][k]]
            deps_a=sorted(rename(n,mapping) for n in a['actual']['dependencies'])
            deps_b=sorted(b['actual']['dependencies'])
            if deps_a!=deps_b:remaining.append('direct_dependencies')
            if a['directAX_any_stored_producer']!=b['directAX_any_stored_producer']:remaining.append('directAX')
            if raw:changes.append({'name':name,'raw_changed_fields':raw})
            if remaining:unresolved.append({'name':name,'unresolved_fields':remaining})
        result['modules'].append({'canonical_module':canonical,'original_module_name':original_name,
          'original_source_sha256':row['sha256'],'adapted_source_sha256':row['adapted_sha256'],
          'mapping':mapping,'dependency_aliases':aliases,'stored_occurrences':len(original),
          'raw_changed_declarations':changes,'unresolved_non_Name_differences':unresolved,
          'qualified_name_correspondence':not unresolved,
          'record_files':{k:{'path':p.name,'sha256':sha(p)} for k,p in paths.items()}})
        save()
    result['complete']=True;result['all_Name_qualified']=all(r['qualified_name_correspondence'] for r in result['modules']);save()
except Exception as exc:
    result['failure']=repr(exc);save();raise
print(json.dumps({'complete':True,'modules':len(result['modules']),'all_Name_qualified':result['all_Name_qualified']}))
