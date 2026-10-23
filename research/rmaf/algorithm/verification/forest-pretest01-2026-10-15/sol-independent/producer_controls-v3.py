#!/usr/bin/env python3
"""One-shot synthetic calibration of the independent stored-producer recorder."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import traceback

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[6]
LEAN=Path('/Users/paurel/Documents/ChatGPT/bootscience/.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean')

def require(condition,message):
    if not condition:
        raise AssertionError(message)

def execute(module,compile_olean,log,expected_import_refusal=False):
    command=[str(LEAN)]
    if compile_olean:
        command+=['-o',module+'.olean']
    command+=[module+'.lean']
    environment=dict(os.environ)
    environment['LEAN_PATH']=str(HERE)
    start=time.perf_counter()
    row={'module':module,'command':command,'timeout_seconds':60}
    try:
        p=subprocess.run(command,cwd=HERE,env=environment,text=True,capture_output=True,timeout=60)
        row.update(exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr,
                   status='PASS' if p.returncode==0 else 'FAIL')
    except subprocess.TimeoutExpired as error:
        row.update(status='TIMEOUT',stdout=str(error.stdout or ''),stderr=str(error.stderr or ''))
    row['seconds']=time.perf_counter()-start
    row['source_sha256']=hashlib.sha256((HERE/(module+'.lean')).read_bytes()).hexdigest()
    log.append(row)
    if expected_import_refusal:
        require(row['status']=='FAIL' and "environment already contains 'PlantCollision.shared'" in row['stdout'],
                'wrong collision refusal: '+module)
        row['expected_collision_refusal']=True
        return []
    require(row['status']=='PASS','command failed: '+module)
    return [json.loads(line[len('PRODUCER '):]) for line in row['stdout'].splitlines()
            if line.startswith('PRODUCER ')]

def producer_rows(rows,layer='raw-module'):
    return [r for r in rows if r['layer']==layer]

def by_name(rows,name):
    return [r for r in producer_rows(rows) if r['producer']['name']==name]

def refs(producer,which):
    value=producer[which]
    return set() if value is None else set(value['refs'])

def decode_literal(dag):
    # Calibration-only literal payload, not a general Lean value evaluator:
    # elaborated Nat numerals are OfNat applications, retaining one nat node.
    payloads={node[1] for node in dag['nodes'] if node[0]=='nat'}
    return next(iter(payloads)) if len(payloads)==1 else None

def controls(rows_ab,rows_ba):
    checks=[]
    def check(name,test,detail):
        require(test,name)
        checks.append({'id':name,'pass':True,'detail':detail})
    raw=producer_rows(rows_ab)
    axioms=[r for r in raw if r['producer']['kind']=='axiom']
    clean=[r for r in raw if r['module']=='PlantClean']
    check('clean_twin',len(clean)==3 and not any(r['producer']['kind']=='axiom' for r in clean),
          {'producers':len(clean)})
    foreign=by_name(rows_ab,'PlantForeign.foreignFalse')
    check('foreign_public_axiom',len(foreign)==1 and foreign[0]['producer']['kind']=='axiom',
          {'origin':foreign[0]['module'] if foreign else None})
    private=[r for r in axioms if '_private' in r['producer']['name'] and 'hiddenPrivate' in r['producer']['name']]
    check('private_axiom',len(private)==1 and private[0]['module']=='PlantPrivate',
          {'actual_names':[r['producer']['name'] for r in private]})
    unused=by_name(rows_ab,'PlantUnused.unusedNat')
    refs_all=set().union(*(refs(r['producer'],'type')|refs(r['producer'],'body') for r in raw))
    check('unused_axiom',len(unused)==1 and unused[0]['producer']['kind']=='axiom'
          and 'PlantUnused.unusedNat' not in refs_all,{'still_stored':len(unused)})
    body=by_name(rows_ab,'PlantBodyOnly.value')[0]['producer']
    check('body_only_hidden_axiom','PlantBodyOnly.hiddenValue' not in refs(body,'type')
          and 'PlantBodyOnly.hiddenValue' in refs(body,'body')
          and by_name(rows_ab,'PlantBodyOnly.hiddenValue')[0]['producer']['kind']=='axiom',
          {'type_refs':sorted(refs(body,'type')),'body_refs':sorted(refs(body,'body'))})
    lookup={r['producer']['name']:r['producer'] for r in raw}
    def closure(name):
        pending=[name]
        reached=set()
        while pending:
            current=pending.pop()
            if current in reached:
                continue
            reached.add(current)
            if current in lookup:
                producer=lookup[current]
                pending.extend(refs(producer,'type')|refs(producer,'body'))
                for rule in producer['rules']:
                    pending.extend(rule['rhs']['refs'])
        return reached
    chain=by_name(rows_ab,'PlantBodyOnly.chain')[0]['producer']
    check('transitive_body_axiom','PlantBodyOnly.hiddenValue' not in refs(chain,'body')
          and 'PlantBodyOnly.hiddenValue' in closure('PlantBodyOnly.chain'),
          {'direct_body_refs':sorted(refs(chain,'body')),'reached_axiom':'PlantBodyOnly.hiddenValue'})
    exposed=by_name(rows_ab,'PlantPrivate.exposed')[0]['producer']
    check('private_body_reference',any('_private' in n and 'hiddenPrivate' in n for n in refs(exposed,'body')),
          {'body_refs':sorted(refs(exposed,'body'))})
    opaque=by_name(rows_ab,'PlantClean.opaqueClean')[0]['producer']
    check('opaque_body',opaque['kind']=='opaque' and opaque['body'] is not None
          and 'True.intro' in refs(opaque,'body'),{'kind':opaque['kind'],'body_refs':sorted(refs(opaque,'body'))})
    collision_pair=by_name(rows_ab,'PlantCollision.shared')+by_name(rows_ba,'PlantCollision.shared')
    values=[decode_literal(r['producer']['body']) for r in collision_pair]
    check('raw_collision_before_combining',len(collision_pair)==2 and set(values)=={7,11}
          and collision_pair[0]['producer']['type']==collision_pair[1]['producer']['type'],
          {'origins':[r['module'] for r in collision_pair],'values':values})
    for label,rows in [('A',rows_ab),('B',rows_ba)]:
        collision=by_name(rows,'PlantCollision.shared')
        values=[decode_literal(r['producer']['body']) for r in collision]
        check('separate_value_'+label,len(collision)==1 and values==([7] if label=='A' else [11]),
              {'origins':[r['module'] for r in collision],'values':values})
        merged=[r for r in producer_rows(rows,'coalesced') if r['producer']['name']=='PlantCollision.shared']
        check('coalesced_observed_'+label,len(merged)==1 and merged[0]['origin'] in ('PlantCollisionA','PlantCollisionB'),
              {'origin':merged[0]['origin'] if merged else None,
               'value':decode_literal(merged[0]['producer']['body']) if merged else None})
    ab=collision_pair
    check('different_nonproof_values',ab[0]['producer']['type']==ab[1]['producer']['type']
          and ab[0]['producer']['body']!=ab[1]['producer']['body'],{})
    # A detector which looks only at reachable proof types must demonstrably miss these.
    broken_type_only='PlantBodyOnly.hiddenValue' in refs(body,'type')
    check('type_only_detector_rejected',not broken_type_only and 'PlantBodyOnly.hiddenValue' in refs(body,'body'),{})
    comparison_raw=raw+[r for r in producer_rows(rows_ba) if r['module']=='PlantCollisionB']
    broken_name_coalescer={r['producer']['name']:r for r in comparison_raw}
    check('name_only_coalescer_rejected',len(broken_name_coalescer)<len(comparison_raw),
          {'raw_occurrences':len(comparison_raw),'after_broken_coalescence':len(broken_name_coalescer)})
    check('axiom_denominator',len(axioms)==4,{'axioms':len(axioms)})
    return checks

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--pilot',action='store_true')
    p.add_argument('--out',required=True)
    a=p.parse_args()
    out=Path(a.out)
    require(not out.exists(),'refuse evidence overwrite')
    start=time.perf_counter()
    result={'phase':'prerelease','pilot':a.pilot,'commands':[],'controls':[],
            'recorder_sha256':hashlib.sha256((HERE/'ProducerAudit.lean').read_bytes()).hexdigest(),
            'runtime_binary_sha256':hashlib.sha256(LEAN.read_bytes()).hexdigest(),
            'disk_free_before':shutil.disk_usage(HERE).free}
    try:
        require(result['disk_free_before']>=3*2**30,'3 GiB floor before')
        if a.pilot:
            execute('PlantClean',True,result['commands'])
            rows=execute('PlantScanClean',False,result['commands'])
            raw=producer_rows(rows)
            require(len(raw)==3,'pilot producer denominator')
            require(not any(r['producer']['kind']=='axiom' for r in raw),'pilot clean false alarm')
            require(all(r['producer']['body'] is not None for r in raw),'pilot body unavailable')
            result['pilot_raw_producers']=len(raw)
        else:
            for module in ('PlantForeign','PlantPrivate','PlantUnused','PlantBodyOnly','PlantCollisionA','PlantCollisionB'):
                execute(module,True,result['commands'])
            rows_ab=execute('PlantScanA',False,result['commands'])
            rows_ba=execute('PlantScanB',False,result['commands'])
            result['controls']=controls(rows_ab,rows_ba)
            execute('PlantScanAB',False,result['commands'],True)
            execute('PlantScanBA',False,result['commands'],True)
            result['controls'].append({'id':'both_import_orders_refuse','pass':True})
            execute('DagCalibration',False,result['commands'])
            require('DAG-CONTROL PASS' in result['commands'][-1]['stdout'],'DAG calibration denominator')
            result['controls'].append({'id':'structural_dag_and_metadata_refusal','pass':True})
        result['status']='PASS'
    except BaseException:
        result['status']='FAIL'
        result['failure']=traceback.format_exc()
    finally:
        result['seconds']=time.perf_counter()-start
        result['disk_free_after']=shutil.disk_usage(HERE).free
        if result['disk_free_after']<3*2**30:
            result['status']='FAIL'
            result['resource_failure']='3 GiB floor after'
        out.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({k:result[k] for k in ('status','pilot','seconds','disk_free_after')}
                         | {'commands':len(result['commands']),'controls':len(result['controls']),'receipt':str(out)}))
    return 0 if result['status']=='PASS' else 1

if __name__=='__main__':
    raise SystemExit(main())
