#!/usr/bin/env python3
"""One-shot Std-only audit controls; fresh Lean environment/origin instrument."""
import argparse, collections, datetime, hashlib, json, os, pathlib, shutil, subprocess, time
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[5]
LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
ALLOWED={'propext','Classical.choice','Quot.sound'}

def compare_inventory(got,expected):
    names=[r['name'] for r in got]
    if len(names)!=len(set(names)): raise AssertionError('duplicate-origin')
    if set(names)!=set(expected): raise AssertionError({'origin-mismatch':sorted(set(names)^set(expected))})
    if any(not r['origin'].startswith('Toy') for r in got): raise AssertionError('wrong-module-origin')
    return True

def reject_custom_axioms(rows):
    findings=[]
    for r in rows:
        if r['kind']=='axiom' and r['name'] not in ALLOWED: findings.append({'direct':r['name'],'origin':r['origin']})
        for a in r['axioms']:
            if a not in ALLOWED: findings.append({'dependency':a,'from':r['name']})
    if findings: raise AssertionError(findings)
    return True

def rows_from(output,tag):
    rows=[]
    for line in output.splitlines():
        if line.startswith('ROW\t'+tag+'\t'):
            _,_,name,origin,kind,axs=line.split('\t')
            rows.append({'name':name,'origin':origin,'kind':kind,'axioms':axs.split(',') if axs else []})
    return sorted(rows,key=lambda r:r['name'])

def expect_catch(label,fn,rows):
    try: fn(rows)
    except AssertionError as e: return {'id':label,'caught':True,'finding':str(e)}
    raise AssertionError('uncaught '+label)

def main():
    p=argparse.ArgumentParser(); p.add_argument('--pilot',action='store_true'); p.add_argument('--out',required=True); a=p.parse_args()
    spec=json.loads((HERE/'AUDIT-EXPECTATIONS-v1.json').read_text())
    build=HERE/('toy-pilot-v2' if a.pilot else 'toy-fixed-v2'); build.mkdir(exist_ok=True)
    logs=build/'logs'; logs.mkdir(exist_ok=True)
    for src in sorted((HERE/'toys').glob('*.lean')): shutil.copyfile(src,build/src.name)
    env={**os.environ,'LEAN_PATH':str(build)}; records=[]; start=time.perf_counter()
    def run(label,args,want=0):
        t=time.perf_counter(); r=subprocess.run([str(LEAN),*args],cwd=build,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
        (logs/(label+'.log')).write_text(r.stdout)
        rec={'label':label,'exit':r.returncode,'seconds':time.perf_counter()-t,'log':str(logs/(label+'.log'))}; records.append(rec)
        if (r.returncode==0)!=(want==0): raise AssertionError({'unexpected-exit':rec,'output':r.stdout})
        return r.stdout
    run('compile-Auditor',['-o','Auditor.olean','Auditor.lean'])
    run('compile-ToyClean',['-o','ToyClean.olean','ToyClean.lean'])
    (build/'ProbeClean.lean').write_text('import Auditor\nimport ToyClean\n#sol_inventory "clean"\n')
    output=run('inventory-clean',['ProbeClean.lean']); clean=rows_from(output,'clean')
    compare_inventory(clean,spec['cleanOrigins']); reject_custom_axioms(clean)
    result={'phase':'pilot' if a.pilot else 'fixed','status':'CONTROLS-PASS','clean':clean,'records':records}
    if not a.pilot:
        modules=['ToyPublic','ToyPrivate','ToyHidden','ToyImported','ToyUsed','ToyGenerated','ToyTrue']
        for mod in modules: run('compile-'+mod,['-o',mod+'.olean',mod+'.lean'])
        catches=[]; axiomRows={}
        for mod in ['ToyPublic','ToyPrivate','ToyImported','ToyUsed']:
            probe='Probe'+mod+'.lean'; (build/probe).write_text('import Auditor\nimport '+mod+'\n#sol_inventory "'+mod+'"\n')
            rows=rows_from(run('inventory-'+mod,[probe]),mod); assert rows
            axiomRows[mod]=rows; catches.append(expect_catch(mod,reject_custom_axioms,rows))
        falseOut=run('compile-explicit-false',['ToyFalse.lean'],want=1)
        assert 'error' in falseOut.lower(); catches.append({'id':'explicit-false-lean','caught':True})
        (build/'ProbeGenerated.lean').write_text('import Auditor\nimport ToyGenerated\n#sol_inventory "before"\n#check ToyGenerated.bump.eq_1\n#sol_inventory "after"\n')
        generatedOut=run('inventory-generated',['ProbeGenerated.lean']); before=rows_from(generatedOut,'before'); after=rows_from(generatedOut,'after')
        names=[r['name'] for r in after]; assert spec['generated']['requiredMain'] in names; assert spec['generated']['forcedEquation'] in names
        assert next(r for r in after if r['name']==spec['generated']['forcedEquation'])['origin']==spec['generated']['expectForcedOrigin']
        reject_custom_axioms(after); compare_inventory(after,names)
        catches.append(expect_catch('missing-generated-origin',lambda r:compare_inventory(r,names),[r for r in after if r['name']!=spec['generated']['forcedEquation']]))
        catches.append(expect_catch('missing-origin',lambda r:compare_inventory(r,spec['cleanOrigins']),clean[1:]))
        catches.append(expect_catch('duplicate-origin',lambda r:compare_inventory(r,spec['cleanOrigins']),clean+[clean[0]]))
        corrupt=[dict(r) for r in clean]; corrupt[0]['origin']='Wrong'; catches.append(expect_catch('wrong-module-origin',lambda r:compare_inventory(r,spec['cleanOrigins']),corrupt))
        assert len(catches)==9
        result.update({'axiomRows':axiomRows,'generatedBefore':before,'generatedAfter':after,'catches':catches,'compiledToyModuleCount':8,'expectedCompiledToyModuleCount':8})
    result['seconds']=time.perf_counter()-start; result['expectationsSHA256']=hashlib.sha256((HERE/'AUDIT-EXPECTATIONS-v1.json').read_bytes()).hexdigest()
    pathlib.Path(a.out).write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps({'status':result['status'],'phase':result['phase'],'records':len(records),'seconds':result['seconds']}))
if __name__=='__main__': main()
