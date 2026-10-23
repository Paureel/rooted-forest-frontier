#!/usr/bin/env python3
"""Strict Name-slot-only classification of original-basename counterparts."""
from copy import deepcopy
import json
from pathlib import Path
import re
HERE=Path(__file__).resolve().parent


def lexical_name(s):
    out=[];quoted=False;escaped=False;guillemet=0
    for ch in s:
        if quoted:
            out.append(ch)
            if escaped:escaped=False
            elif ch=='\\':escaped=True
            elif ch=='"':quoted=False
        elif ch=='"':quoted=True;out.append(ch)
        elif ch=='«':guillemet+=1;out.append(ch)
        elif ch=='»':guillemet-=1;out.append(ch)
        elif ch.isspace() and not guillemet:continue
        else:out.append(ch)
    return ''.join(out)


def name_map(s,mapping):
    if '_private' not in s and '«_@»' not in s:return s
    for old,new in mapping.items():
        s=re.sub(r'(_private\.|«_@»\.)'+re.escape(old)+r'(?=\.|\s|$)',lambda m:m.group(1)+new,s)
        s=s.replace('"'+old+'"','"'+new+'"')
    return lexical_name(s)


def dag_map(dag,mapping):
    if dag is None:return None
    out=deepcopy(dag)
    for row in out['nodes']:
        tag=row[0]
        if tag in ['const','lam','forallE','letE','proj','fvar','mvar','sort']:
            row[1]=name_map(row[1],mapping)
        if tag=='const':row[2]=[name_map(s,mapping) for s in row[2]]
        if tag=='mdata':row[1]=name_map(row[1],mapping)
        # Literal nodes are deliberately untouched, including private-looking strings.
    return out


def extra_map(x,mapping,key=None):
    if isinstance(x,dict):
        if x.get('encoding')=='exact-Expr-DAG-v1':return dag_map(x,mapping)
        return {k:extra_map(v,mapping,k) for k,v in x.items()}
    if isinstance(x,list):return [extra_map(v,mapping,key) for v in x]
    if isinstance(x,str) and key in ['constructors','all','inductive','constructor']:return name_map(x,mapping)
    return x


def actual_map(a,mapping):
    return {'kind':a['kind'],'type':dag_map(a['type'],mapping),'body':dag_map(a['body'],mapping),
        'extra':extra_map(a['extra'],mapping),'universe_parameters':[name_map(s,mapping) for s in a['universe_parameters']],
        'unsafe':a['unsafe'],'partial':a['partial'],
        'dependencies':sorted(name_map(s,mapping) for s in a['dependencies'])}


result={'context':'post-contact Name-slot diagnosis; no raw equality retrofit','controls':[],'modules':[]}
try:
    mapping={'Embedding':'GroupEmbedding'}
    old='Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkNum `a.«_@»._internal 0) "Embedding") 72'
    new=old.replace('"Embedding"','"GroupEmbedding"')
    assert name_map(old,mapping)==name_map(new,{})
    negatives=[('numeric hygiene id change',name_map(old,mapping),name_map(new.replace('72','73'),{})),
      ('public symbol change',name_map('RestrictionBridge.good',mapping),name_map('RestrictionBridge.bad',{})),
      ('unmarked alpha/beta binder change',name_map('`alpha',mapping),name_map('`beta',{})),
      ('binder annotation change','Lean.BinderInfo.default','Lean.BinderInfo.implicit')]
    for label,a,b in negatives:
        assert a!=b,'Name rule accepted '+label;result['controls'].append({'plant':label,'caught':True})
    lit={'encoding':'exact-Expr-DAG-v1','root':0,'nodes':[['literal','"_private.Embedding.payload"']]}
    false={'encoding':'exact-Expr-DAG-v1','root':0,'nodes':[['literal','"_private.GroupEmbedding.payload"']]}
    assert dag_map(lit,mapping)!=dag_map(false,{}),'Name rule rewrote a literal'
    result['controls'].append({'plant':'literal string payload containing a private-looking name','caught':True})
    source=json.loads((HERE/'natural-module-alias-review-v1.json').read_text());assert source['complete']
    for module in source['modules']:
        a=json.loads((HERE/module['record_files']['original']['path']).read_text())
        b=json.loads((HERE/module['record_files']['canonical']['path']).read_text());mapping=module['mapping']
        a={name_map(r['name'],mapping):r for r in a['occurrences']}
        b={name_map(r['name'],{}):r for r in b['occurrences']}
        assert set(a)==set(b),'natural declaration names differ beyond declared Name map'
        unresolved=[];changed=[]
        for n in a:
            aa=actual_map(a[n]['actual'],mapping);bb=actual_map(b[n]['actual'],{})
            fields=[k for k in aa if aa[k]!=bb[k]]
            if fields:unresolved.append({'name':n,'fields':fields})
            if a[n]['actual']!=b[n]['actual']:changed.append(n)
            assert a[n]['directAX_any_stored_producer']==b[n]['directAX_any_stored_producer']
        result['modules'].append({'canonical_module':module['canonical_module'],'original_module_name':module['original_module_name'],
            'mapping':mapping,'stored_occurrences':len(a),'qualified_Name_and_Name_repr_only':not unresolved,
            'raw_different_records':changed,'unresolved':unresolved})
    result['unresolved']=[r for m in result['modules'] for r in m['unresolved']]
    result['passed']=not result['unresolved']
    assert result['passed'],'non-Name structural original/canonical differences remain unaccepted'
except Exception as exc:
    result['passed']=False;result['failure']=repr(exc);raise
finally:(HERE/'natural-name-classification-v1.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'modules':len(result['modules']),'unresolved':len(result['unresolved']),'false_twins':len(result['controls'])}))
