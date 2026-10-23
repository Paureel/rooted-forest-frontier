#!/usr/bin/env python3
"""One-shot independent Std-only stored-producer control driver.
No candidate modules; source pins and per-command logs are retained.
"""
import argparse, copy, hashlib, json, os
from pathlib import Path
import subprocess, time

ROOT=Path(__file__).resolve().parents[7]
HERE=Path(__file__).resolve().parent
ORIGIN=HERE/'origin'
LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
PINS=json.loads((ORIGIN/'SOURCE-PINS-v1.json').read_text())
ALLOW={'propext','Classical.choice','Quot.sound'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def verify_sources(base=ORIGIN):
    for name,digest in PINS.items():
        if sha(base/name)!=digest: raise ValueError('exact byte pin: '+name)

def run(command,cwd,search,label,records):
    env=dict(os.environ); env['LEAN_PATH']=str(search)
    at=time.perf_counter()
    r=subprocess.run([str(LEAN)]+command,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
    sec=time.perf_counter()-at
    (HERE/(label+'.log')).write_text(r.stdout)
    records.append({'label':label,'command':[str(LEAN)]+command,'cwd':str(cwd),'LEAN_PATH':str(search),'returncode':r.returncode,'seconds':sec,'log':label+'.log'})
    return r

def compile_one(name,source,build,label,records,expected=0):
    build.mkdir(exist_ok=True,parents=True)
    r=run(['-o',str(build/(name+'.olean')),str(source/(name+'.lean'))],source,build,label,records)
    if (r.returncode==0)!=(expected==0): raise ValueError('compile expectation '+name+': '+str(r.returncode))
    return r

def audit(modules,build,label,records):
    r=run(['--run',str(ORIGIN/'ProducerAudit_v1.lean')]+modules,ORIGIN,build,label,records)
    if r.returncode: raise ValueError('audit tool failed '+label)
    obj=json.loads(r.stdout)
    for row in obj['rows']:
        row['type_sha256']=hashlib.sha256(row['type'].encode()).hexdigest()
        row['body_sha256']=None if row['body'] is None else hashlib.sha256(row['body'].encode()).hexdigest()
    (HERE/(label+'.json')).write_text(json.dumps(obj,indent=2)+'\n')
    return obj

def fingerprint(obj):
    return sorted((r['producer'],r['index'],r['name'],r['kind'],r['type_sha256'],r['body_sha256']) for r in obj['rows'])

def gate(obj,modules,expected_imports=None,expected_fingerprint=None):
    if obj['trustLevel']!=0: raise ValueError('nonzero trust level')
    headers=obj['producers']; rows=obj['rows']
    if len(headers)!=len(modules) or {h['module'] for h in headers}!=set(modules): raise ValueError('producer coverage')
    if {r['producer'] for r in rows}!=set(modules): raise ValueError('row producer coverage')
    keys=[(r['producer'],r['index'],r['name']) for r in rows]
    if len(keys)!=len(set(keys)): raise ValueError('duplicate occurrence')
    for h in headers:
        rr=[r for r in rows if r['producer']==h['module']]
        if sorted(r['index'] for r in rr)!=list(range(h['count'])): raise ValueError('missing/duplicate occurrence index')
        if expected_imports is not None and h['imports']!=expected_imports[h['module']]: raise ValueError('actual stored import changed')
        if h['module'] in {'CleanA','CleanB','HostileCoalesced','UnusedAxiom','PrivateAxiom'}:
            minimum={'CleanA':3,'CleanB':2,'HostileCoalesced':2,'UnusedAxiom':2,'PrivateAxiom':2}[h['module']]
            if h['count']<minimum: raise ValueError('named declarations missing')
    for r in rows:
        if not r['type'] or r['resolved_origin']=='UNRESOLVED' or r['missing']: raise ValueError('unresolved actual occurrence '+r['name'])
        if r['kind'] in {'theorem','definition','opaque'} and r['body'] is None: raise ValueError('stored body absent')
        if r['kind']=='axiom' and r['name'] not in ALLOW: raise ValueError('direct custom axiom '+r['producer']+':'+r['name'])
        if set(r['axioms'])-ALLOW: raise ValueError('custom axiom closure '+r['name'])
        if hashlib.sha256(r['type'].encode()).hexdigest()!=r['type_sha256']: raise ValueError('type hash changed')
        if r['body'] is not None and hashlib.sha256(r['body'].encode()).hexdigest()!=r['body_sha256']: raise ValueError('body hash changed')
    if expected_fingerprint is not None and fingerprint(obj)!=expected_fingerprint: raise ValueError('exact stored type/body adaptation')
    return True

def must_reject(name,fn,results):
    try: fn()
    except (ValueError,AssertionError) as ex: results.append({'control':name,'reject':True,'reason':str(ex)})
    else: raise AssertionError('hostile control survived: '+name)

def main():
    p=argparse.ArgumentParser(); p.add_argument('mode',choices=['pilot','full']); a=p.parse_args()
    records=[]; controls=[]; result={'mode':a.mode,'candidate_contact':False,'commands':records,'controls':controls,'script_sha256':sha(Path(__file__)),'source_pins_sha256':sha(ORIGIN/'SOURCE-PINS-v1.json')}
    out=HERE/('origin-'+a.mode+'-run1.json')
    try:
        verify_sources()
        run(['--version'],ORIGIN,ORIGIN,'origin-version-'+a.mode,records)
        build=ORIGIN/('build-'+a.mode)
        modules=['CleanA','CleanB'] if a.mode=='pilot' else ['CleanA','CleanB','HostileCoalesced','UnusedAxiom','PrivateAxiom','GeneratedPrivateClean','KnownFalseCompile']
        for m in modules: compile_one(m,ORIGIN,build,'origin-compile-'+a.mode+'-'+m,records,expected=1 if m=='KnownFalseCompile' else 0)
        cases=[(['CleanA'],True),(['CleanA','CleanB'],True)]
        if a.mode=='full': cases += [(['GeneratedPrivateClean'],True),(['UnusedAxiom'],False),(['PrivateAxiom'],False),(['CleanA','PrivateAxiom'],False),(['CleanA','HostileCoalesced'],False)]
        baseline=None
        for ms,clean in cases:
            name='+'.join(ms); obj=audit(ms,build,'origin-'+a.mode+'-'+name,records)
            expected_imports={m:['Std'] for m in ms}
            if clean:
                gate(obj,ms,expected_imports); controls.append({'control':name,'pass':True,'stored_occurrences':len(obj['rows']),'resolved_unique_names':len({r['name'] for r in obj['rows']})})
            else: must_reject(name,lambda:gate(obj,ms,expected_imports),controls)
            if ms==['CleanA']: baseline=obj
            if ms==['CleanA','CleanB']:
                twins=[r for r in obj['rows'] if r['name']=='BlindPlant.shared']
                assert len(twins)==2 and all(r['kind']=='theorem' for r in twins)
            if ms==['CleanA','HostileCoalesced']:
                twins=[r for r in obj['rows'] if r['name']=='BlindPlant.shared']
                assert len(twins)==2 and {r['kind'] for r in twins}=={'axiom','theorem'}
                controls.append({'control':'coalesced-direct-inspection','pass':True,'rows':twins})
            if ms==['GeneratedPrivateClean']:
                assert any(r['name'].startswith('_private.') for r in obj['rows'])
                assert any(r['name']=='BlindGenerated.Token.rec' for r in obj['rows'])
                controls.append({'control':'private-generated-coverage','pass':True,'rows':len(obj['rows'])})
        if a.mode=='full':
            missing=copy.deepcopy(baseline); missing['rows'].pop(); must_reject('MissingOccurrence',lambda:gate(missing,['CleanA']),controls)
            duplicate=copy.deepcopy(baseline); duplicate['rows'].append(copy.deepcopy(duplicate['rows'][0])); must_reject('DuplicateOccurrence',lambda:gate(duplicate,['CleanA']),controls)
            body=copy.deepcopy(baseline); row=next(r for r in body['rows'] if r['body'] is not None); row['body']+='CORRUPT'
            must_reject('ChangedBodyReceipt',lambda:gate(body,['CleanA']),controls)
            adapt=ORIGIN/'adaptations'; adapt.mkdir(exist_ok=True)
            source=(ORIGIN/'CleanA.lean').read_text()
            byte=adapt/'byte'; byte.mkdir(exist_ok=True); (byte/'CleanA.lean').write_text(source+'\n')
            def byte_check():
                if sha(byte/'CleanA.lean')!=PINS['CleanA.lean']: raise ValueError('exact source byte adaptation')
            must_reject('ChangedSourceByte',byte_check,controls)
            for tag,changed in [('body',source.replace(':= 7',':= 8')),('import',source.replace('import Std','import Lean'))]:
                folder=adapt/tag; folder.mkdir(exist_ok=True); (folder/'CleanA.lean').write_text(changed)
                abuild=folder/'build'; compile_one('CleanA',folder,abuild,'origin-adapt-'+tag+'-compile',records)
                obj=audit(['CleanA'],abuild,'origin-adapt-'+tag+'-audit',records)
                if tag=='body': must_reject('ChangedBodyActual',lambda:gate(obj,['CleanA'],{'CleanA':['Std']},fingerprint(baseline)),controls)
                else: must_reject('ChangedImportActual',lambda:gate(obj,['CleanA'],{'CleanA':['Std']}),controls)
        verify_sources(); result['status']='CONTROLS_PASS' if a.mode=='full' else 'PILOT_PASS'
    except Exception as ex:
        result['status']='FAIL'; result['error']=repr(ex); raise
    finally:
        result['total_command_seconds']=sum(c['seconds'] for c in records)
        out.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({'mode':a.mode,'status':result['status'],'controls':len(controls),'seconds':result['total_command_seconds'],'receipt':str(out)}))
if __name__=='__main__': main()
