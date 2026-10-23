#!/usr/bin/env python3
"""New-boundary stored-producer qualifier; no candidate source inputs."""
from collections import Counter
from copy import deepcopy
import json
import os
from pathlib import Path
import subprocess
import sys
import time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[6]
TOYS=HERE/'producer-toys'
mode=sys.argv[1]
spec=json.loads((HERE/'PRODUCER-EXPECTATIONS-v1.json').read_text())
out=HERE/('producer-'+mode+'-v4.json')
result={'mode':mode,'candidate_contact':True,'scope':'post-contact representation requalification on own Std toys','new_boundary_detector':True,'commands':[],'gates':[]}


def save(): out.write_text(json.dumps(result,indent=2)+'\n')


def run(cmd,cwd=TOYS,extra_path=None):
    paths=[str(cwd),str(TOYS)]
    if extra_path is not None: paths.append(str(extra_path))
    env={**os.environ,'LEAN_PATH':os.pathsep.join(paths)}
    started=time.perf_counter()
    p=subprocess.run(cmd,cwd=cwd,env=env,text=True,capture_output=True,timeout=30)
    result['commands'].append({'command':cmd,'cwd':str(cwd),'LEAN_PATH':env['LEAN_PATH'],
        'seconds':time.perf_counter()-started,'returncode':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
    save()
    assert p.returncode==0, 'producer command failed'


def compile(mod): run([str(ROOT/'bootloops-lean'),'-o',mod+'.olean',mod+'.lean'])


def audit(root,producers,label,cwd=TOYS,extra_path=None):
    path=HERE/(label+'-occurrences-v4.json')
    run([str(ROOT/'bootloops-lean'),'--run',str(HERE/'producer_audit_v4.lean'),root,str(path),*producers],cwd,extra_path)
    return json.loads(path.read_text())


def occurrence_gate(data,producers,expected_count=None):
    assert set(data['requested_producers'])==set(producers), 'producer request mismatch'
    rows=data['occurrences']
    keys=[(r['producer'],r['ordinal'],r['name']) for r in rows]
    assert len(keys)==len(set(keys)), 'duplicate producer occurrence'
    assert len(rows)==data['occurrence_count'], 'declared occurrence total mismatch'
    counts={r['producer']:r['stored_count'] for r in data['producer_counts']}
    assert set(counts)==set(producers), 'missing producer module'
    assert Counter(r['producer'] for r in rows)==Counter(counts), 'missing stored occurrence'
    if expected_count is not None: assert len(rows)==expected_count, 'literal occurrence denominator mismatch'
    bad=[]
    for r in rows:
        assert r['actual']['name']==r['name'] and r['actual']['origin']==r['producer'], 'actual producer mismatch'
        assert not r['unresolved_dependencies'], 'unresolved actual-body dependency'
        assert r['resolved'] is not None, 'unresolved producer declaration'
        assert r['actual']['kind'] in ['axiom','definition','theorem','opaque','quotient','inductive','constructor','recursor']
        if r['actual']['kind'] in ['definition','theorem','opaque']:
            assert r['actual']['body'] is not None, 'missing actual producer body'
        if r['actual_is_direct_axiom'] or r['actual']['kind']=='axiom': bad.append((r['producer'],r['name']))
        assert set(r['directAX_resolved'])<=set(r['actual']['dependencies']), 'directAX not a direct reference'
    assert not bad, 'direct custom stored axiom(s): '+repr(bad)
    return len(rows)


def caught(name,call):
    try: call()
    except AssertionError as exc:
        result['gates'].append({'name':name,'caught':True,'message':str(exc)});save();return
    raise AssertionError('SURVIVING PRODUCER FALSE PLANT '+name)


def semantic_records(data):
    # Exact scientific records keyed by stored occurrence, independent of import
    # DAG module positions. No type/body/name rewriting or normalization.
    return {(r['producer'],r['ordinal'],r['name']):{k:r[k] for k in [
      'actual','resolved_origin','resolved','actual_is_direct_axiom',
      'directAX_resolved','directAX_any_stored_producer','unresolved_dependencies']}
      for r in data['occurrences']}


def exact_adapter(a,b): assert semantic_records(a)==semantic_records(b), 'exact stored type/body/directAX records differ'


try:
    if mode=='pilot':
        compile('ProducerA')
        data=audit('ProducerA',['ProducerA'],'producer-pilot')
        occurrence_gate(data,['ProducerA'],2)
        result['gates'].append({'name':'fresh tiny stored producer pilot','passed':True,'occurrences':2})
    elif mode=='battery':
        for m in ['ProducerA','ProducerB','ProducerHostile','ProducerPrivate','TopClean','TopHostile']: compile(m)
        clean=audit('TopClean',spec['clean']['producers'],'producer-clean')
        occurrence_gate(clean,spec['clean']['producers'],4)
        assert len({r['name'] for r in clean['occurrences']})==3
        result['gates'].append({'name':'clean coalesced theorem twin','passed':True,'occurrences':4,'unique_names':3})
        hostile=audit('TopHostile',spec['hostile']['producers'],'producer-hostile')
        old=hostile['resolved_inventory']['records']
        assert not [r for r in old if r['kind']=='axiom'], 'hostile plant did not demonstrate old-gate omission'
        assert len([r for r in hostile['occurrences'] if r['actual_is_direct_axiom']])==1
        assert any(r['producer']=='ProducerHostile' and r['name']=='Coalesced.ownHostile' for r in hostile['occurrences'])
        caught('hostile coalesced axiom',lambda:occurrence_gate(hostile,spec['hostile']['producers'],4))
        private=audit('ProducerPrivate',['ProducerPrivate'],'producer-private')
        assert len(private['occurrences'])==2
        caught('private stored axiom',lambda:occurrence_gate(private,['ProducerPrivate'],2))
        bad=deepcopy(clean);bad['occurrences']=bad['occurrences'][1:]
        caught('missing_stored_occurrence',lambda:occurrence_gate(bad,spec['clean']['producers']))
        bad2=deepcopy(clean);bad2['occurrences'].append(bad2['occurrences'][0]);bad2['occurrence_count']+=1
        caught('duplicate_stored_occurrence',lambda:occurrence_gate(bad2,spec['clean']['producers']))
        bad['occurrence_count']-=1
        caught('forged_total_missing_occurrence',lambda:occurrence_gate(bad,spec['clean']['producers']))
        by_name={r['name']:r for r in clean['occurrences']};bad3=deepcopy(clean)
        bad3['occurrences']=list(by_name.values());bad3['occurrence_count']=len(by_name)
        caught('resolved_only_substitute',lambda:occurrence_gate(bad3,spec['clean']['producers']))
        bad4=deepcopy(clean);bad4['occurrences'][0]['unresolved_dependencies']=['Nonexistent.payload']
        caught('unresolved_dependency_plant',lambda:occurrence_gate(bad4,spec['clean']['producers']))
        parent=HERE.parent
        base=audit('Clean',['Clean'],'producer-adapter-base',parent/'toy-src')
        adapted=audit('Clean',['Clean'],'producer-adapter-import',parent/'toy-literal-import-v3',parent/'toy-src')
        body=audit('Clean',['Clean'],'producer-adapter-body',parent/'toy-literal-body-v3',parent/'toy-src')
        for x in [base,adapted,body]: occurrence_gate(x,['Clean'],14)
        original=(parent/'toy-src/Clean.lean').read_bytes()
        assert (parent/'toy-literal-import-v3/Clean.lean').read_bytes()==original.replace(b'import Std\n',b'import EmptyDependency\n',1)
        assert (parent/'toy-literal-body-v3/Clean.lean').read_bytes()==original.replace(b'def publicPayload : Nat := 7\n',b'def publicPayload : Nat := 8\n',1)
        exact_adapter(base,adapted)
        result['gates'].append({'name':'producer import-only exact byte/type/body/directAX adapter','passed':True,'occurrences':14})
        caught('producer body-only adapter',lambda:exact_adapter(base,body))
        assert len(result['gates'])==10
    else: raise ValueError('pilot or battery')
    result['passed']=True;save();print(json.dumps({'passed':True,'mode':mode,'commands':len(result['commands']),'gates':len(result['gates'])}))
except Exception as exc:
    result['passed']=False;result['failure']=repr(exc);save();raise
