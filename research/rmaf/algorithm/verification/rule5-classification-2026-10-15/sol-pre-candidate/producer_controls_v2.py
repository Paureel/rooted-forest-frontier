#!/usr/bin/env python3
"""One-shot new-scope Std producer qualification using pinned own prior auditor."""
from collections import Counter
from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[5]
TOYS = HERE/'producer-toys'
SPEC = json.loads((HERE/'PRODUCER-EXPECTATIONS-v2.json').read_text())
MODE = sys.argv[1]
OUT = HERE/('producer-'+MODE+'-v2.json')
RESULT = {'context':'classification/prefix PRE-CANDIDATE; reused own exact-DAG instrument',
          'candidate_contact':False,'mode':MODE,'commands':[],'gates':[]}


def save():
    OUT.write_text(json.dumps(RESULT,indent=2)+'\n')


def run(args,cwd):
    start = time.perf_counter()
    env = {**os.environ,'LEAN_PATH':os.pathsep.join([str(cwd),str(HERE/'producer-base'),str(TOYS)])}
    p = subprocess.run(args,cwd=cwd,env=env,text=True,capture_output=True,timeout=30)
    RESULT['commands'].append({'command':args,'cwd':str(cwd),'LEAN_PATH':env['LEAN_PATH'],
        'seconds':time.perf_counter()-start,'returncode':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
    save()
    assert p.returncode == 0, 'control compile/audit failed'


def compile(module,cwd=TOYS):
    run([str(ROOT/'bootloops-lean'),'-o',module+'.olean',module+'.lean'],cwd)


def audit(root,producers,label,cwd=TOYS):
    path = HERE/(label+'-occurrences-v1.json')
    run([str(ROOT/'bootloops-lean'),'--run',str(HERE/'reused/producer_audit_v4.lean'),root,str(path),*producers],cwd)
    return json.loads(path.read_text())


def gate(data,producers):
    assert set(data['requested_producers']) == set(producers)
    rows = data['occurrences']
    keys = [(r['producer'],r['ordinal'],r['name']) for r in rows]
    assert len(keys) == len(set(keys)) == data['occurrence_count']
    counts = {r['producer']:r['stored_count'] for r in data['producer_counts']}
    assert set(counts) == set(producers)
    assert counts == {p:SPEC['literal_counts'][p] for p in producers}
    assert Counter(r['producer'] for r in rows) == Counter(counts)
    for row in rows:
        assert row['actual']['origin'] == row['producer'] and row['actual']['name'] == row['name']
        assert row['resolved'] is not None and not row['unresolved_dependencies']
        assert row['actual']['type'] is not None
        assert row['actual']['kind'] != 'axiom' and not row['actual_is_direct_axiom']
        if row['actual']['kind'] in ('definition','theorem','opaque'):
            assert row['actual']['body'] is not None
        for dependency in row['dependency_producer_map']:
            assert dependency['resolved_origin'] is not None and dependency['stored_producers']
    return rows


def records(data):
    # Legacy ConstantInfo BEq is deliberately excluded: exact rooted DAGs decide.
    fields = ['actual','resolved_origin','resolved','actual_is_direct_axiom',
              'directAX_resolved','directAX_any_stored_producer','unresolved_dependencies']
    return {(r['producer'],r['ordinal'],r['name']):{k:r[k] for k in fields}
            for r in data['occurrences']}


def exact(left,right):
    assert records(left) == records(right), 'stored type/body/origin records differ'


def caught(name,call):
    try:
        call()
    except AssertionError as exc:
        RESULT['gates'].append({'name':name,'caught':True,'message':str(exc)})
        save()
        return
    raise AssertionError('SURVIVING FALSE PLANT '+name)


def same(left,right):
    assert left == right


def binder_gate(dag):
    assert len(dag['nodes']) == SPEC['DAG_body_nodes']
    found = {r[1]:i for i,r in enumerate(dag['nodes']) if r[0] == 'lam'}
    assert all(n in found for n in SPEC['binder_names'])
    assert len({found[n] for n in SPEC['binder_names']}) == 2


try:
    pin = json.loads((HERE/'PRODUCER-CONTROLS-PIN-v2.json').read_text())
    for row in pin['entries']:
        raw = (HERE/row['path']).read_bytes()
        assert len(raw) == row['bytes'] and hashlib.sha256(raw).hexdigest() == row['sha256']
    if MODE == 'pilot':
        compile('ClassA')
        gate(audit('ClassA',['ClassA'],'producer-pilot'),['ClassA'])
        RESULT['gates'].append({'name':'tiny full-path producer pilot','passed':True,'occurrences':2})
    elif MODE == 'battery':
        for module in ['ClassA','ClassB','ClassHostile','ClassPrivate','ClassTopClean','ClassTopHostile','ClassStd','ClassDAG']:
            compile(module)
        for directory,module in [('producer-base','ClassEmpty'),('producer-base','Clean'),('producer-import','Clean'),('producer-body','Clean')]:
            compile(module,HERE/directory)
        clean = audit('ClassTopClean',SPEC['clean_producers'],'producer-clean')
        rows = gate(clean,SPEC['clean_producers'])
        assert len(rows) == SPEC['coalesced_clean_occurrences']
        assert len({r['name'] for r in rows}) == SPEC['coalesced_unique_names']
        RESULT['gates'].append({'name':'coalesced theorem clean twin','passed':True,'occurrences':4,'names':3})
        hostile = audit('ClassTopHostile',SPEC['hostile_producers'],'producer-hostile')
        assert not [r for r in hostile['resolved_inventory']['records'] if r['kind']=='axiom']
        assert any(r['name']=='ClassificationPlant.ownHostile' for r in hostile['occurrences'])
        caught('coalesced_custom_axiom',lambda:gate(hostile,SPEC['hostile_producers']))
        private = audit('ClassPrivate',['ClassPrivate'],'producer-private')
        caught('unused_private_axiom',lambda:gate(private,['ClassPrivate']))
        for name in ['missing_occurrence','duplicate_occurrence','forged_totals','resolved_only_substitute','foreign_actual_origin','missing_actual_body','unresolved_reference']:
            bad = deepcopy(clean)
            if name in ('missing_occurrence','forged_totals'):
                bad['occurrences'].pop()
                if name=='forged_totals':
                    bad['occurrence_count'] -= 1
                    bad['producer_counts'][-1]['stored_count'] -= 1
            elif name=='duplicate_occurrence':
                bad['occurrences'].append(deepcopy(bad['occurrences'][0]));bad['occurrence_count']+=1
            elif name=='resolved_only_substitute':
                bad['occurrences']=list({r['name']:r for r in bad['occurrences']}.values());bad['occurrence_count']=len(bad['occurrences'])
            elif name=='foreign_actual_origin': bad['occurrences'][0]['actual']['origin']='ForeignClassification'
            elif name=='missing_actual_body': bad['occurrences'][0]['actual']['body']=None
            else: bad['occurrences'][0]['unresolved_dependencies']=['ForeignClassification.missing']
            caught(name,lambda b=bad:gate(b,SPEC['clean_producers']))
        base = audit('Clean',['Clean'],'producer-base',HERE/'producer-base')
        adapted = audit('Clean',['Clean'],'producer-import',HERE/'producer-import')
        changed = audit('Clean',['Clean'],'producer-body',HERE/'producer-body')
        br = gate(base,['Clean']);gate(adapted,['Clean']);gate(changed,['Clean'])
        assert sum(r['name'].startswith('_private.') for r in br) == SPEC['private_occurrences_in_Clean']
        generated = sum(any(s in r['name'] for s in ['.match_','._f','._sunfold','._unsafe_rec']) for r in br)
        assert generated == SPEC['generated_occurrences_in_Clean']
        exact(base,adapted)
        assert base['producer_counts'][0]['imports'] == SPEC['literal_stored_imports']['base']
        assert adapted['producer_counts'][0]['imports'] == SPEC['literal_stored_imports']['adapted']
        RESULT['gates'].append({'name':'literal import adapter and all private/generated records','passed':True,'occurrences':14,'private':10,'generated':8})
        caught('body_only_change',lambda:exact(base,changed))
        bad = deepcopy(base);bad['occurrences'][0]['actual']['type']['root'] = -1
        caught('type_only_change',lambda:exact(base,bad))
        original = (HERE/'producer-base/Clean.lean').read_bytes()
        adapt = (HERE/'producer-import/Clean.lean').read_bytes()
        assert adapt == original.replace(SPEC['adapter']['original'].encode(),SPEC['adapter']['adapted'].encode(),1)
        caught('source_byte_corruption',lambda:same(original+b'\n',original))
        caught('adapted_byte_corruption',lambda:same(adapt+b'\n',adapt))
        std = audit('ClassStd',['ClassStd'],'producer-standard');gate(std,['ClassStd'])
        union = sorted({a for r in std['occurrences'] for a in r['actual']['axioms_resolved_name_closure']})
        assert union == SPEC['standard_axiom_union']
        RESULT['gates'].append({'name':'standard axiom clean twin','passed':True,'axioms':union})
        caught('sorryAx_union',lambda:same(sorted(union+['sorryAx']),SPEC['standard_axiom_union']))
        dag = audit('ClassDAG',['ClassDAG'],'producer-DAG');gate(dag,['ClassDAG'])
        body = dag['occurrences'][0]['actual']['body'];binder_gate(body)
        bad = deepcopy(body)
        alpha = next(r for r in bad['nodes'] if r[0]=='lam' and r[1]=='`alpha')
        beta = next(i for i,r in enumerate(bad['nodes']) if r[0]=='lam' and r[1]=='`beta')
        bad['nodes'][beta] = deepcopy(alpha)
        caught('binder_collapse',lambda:binder_gate(bad))
        assert {r['name'] for r in RESULT['gates'] if r.get('caught')} == set(SPEC['false_gates'])
    else:
        raise ValueError('pilot or battery')
    RESULT['passed']=True
except Exception as exc:
    RESULT['passed']=False;RESULT['failure']=repr(exc)
    raise
finally:
    save()
print(json.dumps({'passed':True,'mode':MODE,'commands':len(RESULT['commands']),'gates':len(RESULT['gates'])}))
