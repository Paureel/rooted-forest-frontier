#!/usr/bin/env python3
"""Post-contact classification of raw original/adapter Name-only differences."""
import json
from pathlib import Path
import re
HERE=Path(__file__).resolve().parent
source=json.loads((HERE/'original-adapter-review-v1.json').read_text())


def rename_name_string(s,mapping):
    for old,new in mapping.items():
        marker=re.compile(r'(_private\.|«_@»\.)'+re.escape(old)+r'(?=\.|\s|$)')
        if marker.search(s):
            s=marker.sub(lambda m:m.group(1)+new,s)
            # Repr Name nested hygiene scopes carry the same module as a
            # quoted Name.mkStr component. This occurs inside Name data only.
            s=s.replace('"'+old+'"','"'+new+'"')
    return s


def diffs(a,b,path=''):
    if type(a)!=type(b):yield path,a,b;return
    if isinstance(a,dict):
        if set(a)!=set(b):yield path+'/KEYS',sorted(a),sorted(b)
        for k in a.keys()&b.keys():yield from diffs(a[k],b[k],path+'/'+k)
    elif isinstance(a,list):
        if len(a)!=len(b):yield path+'/LENGTH',len(a),len(b)
        for i,(u,v) in enumerate(zip(a,b)):yield from diffs(u,v,path+'/'+str(i))
    elif a!=b:yield path,a,b


def classify(a,b,mapping):
    leaves=list(diffs(a,b));unexpected=[]
    for path,x,y in leaves:
        if not(isinstance(x,str) and isinstance(y,str) and rename_name_string(x,mapping)==y):unexpected.append((path,x,y))
    return leaves,unexpected


result={'context':'post-contact diagnostic classification; raw exact results unchanged','controls':[],'modules':[]}
try:
    spec=json.loads((HERE/'ADAPTER-NAME-RULE-v1.json').read_text());p=spec['positive']
    assert rename_name_string(p['old'],p['mapping'])==p['new']
    for label,a,b in [('changed numeric hygiene id',p['old'],p['new'].replace('17','18')),
                      ('changed public symbol','Universal233.PaidQueries.run','Universal233.PaidQueries.bad'),
                      ('changed literal payload',7,8),('changed binder annotation','BinderInfo.default','BinderInfo.implicit')]:
        _,unexpected=classify(a,b,p['mapping']);assert unexpected,'name classifier accepted '+label
        result['controls'].append({'plant':label,'caught':True})
    exact=0;name_only=0;decls=0
    for module in source['modules']:
        if not module['differences']:
            exact+=1;result['modules'].append({'module':module['module'],'raw_exact':True,'qualified_name_only':False});continue
        a=json.loads((HERE/module['records']['original']['path']).read_text())
        b=json.loads((HERE/module['records']['adapted']['path']).read_text())
        a={r['name']:r for r in a['occurrences']};b={r['name']:r for r in b['occurrences']}
        mapping={r['original_import']:r['pinned_dependency_module'] for r in module['aliases']}
        changes=[];unresolved=[]
        for d in module['differences']:
            for field in d['fields']:
                left=a[d['name']]['actual'][field];right=b[d['name']]['actual'][field]
                leaves,bad=classify(left,right,mapping)
                changes.append({'declaration':d['name'],'field':field,'changed_leaves':leaves})
                unresolved.extend({'declaration':d['name'],'field':field,'difference':r} for r in bad)
            decls+=1
        result['modules'].append({'module':module['module'],'raw_exact':False,
            'qualified_name_only':not unresolved,'mapping':mapping,'changes':changes,'unresolved':unresolved})
        assert not unresolved,'non-Name structural adapter difference remains unresolved'
        name_only+=1
    result.update({'raw_exact_import_modules':exact,'qualified_name_only_import_modules':name_only,
                   'name_different_stored_declarations':decls,'passed':True})
except Exception as exc:
    result['passed']=False;result['failure']=repr(exc);raise
finally:(HERE/'adapter-name-classification-v1.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['modules','controls']}))
