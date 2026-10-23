#!/usr/bin/env python3
"""One-shot supplemental allowed-axiom twins, frozen before execution."""
import json,os,pathlib,shutil,subprocess,time
from audit_controls_v5 import HERE,LEAN,rows_from,reject_custom_axioms,compare_inventory,expect_catch

def main():
    start=time.perf_counter(); spec=json.loads((HERE/'STANDARD-AXIOM-EXPECTATIONS-v1.json').read_text()); build=HERE/'toy-standard-v1'; build.mkdir(exist_ok=True); logs=build/'logs'; logs.mkdir(exist_ok=True)
    for src in ['AuditorV3','ToyStandard']: shutil.copyfile(HERE/'toys'/(src+'.lean'),build/(src+'.lean'))
    env={**os.environ,'LEAN_PATH':str(build)}; processes=[]
    def run(label,args):
        t=time.perf_counter(); r=subprocess.run([str(LEAN),*args],cwd=build,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=60)
        (logs/(label+'.log')).write_text(r.stdout); processes.append({'label':label,'exit':r.returncode,'seconds':time.perf_counter()-t})
        assert r.returncode==0,r.stdout
        return r.stdout
    run('compile-AuditorV3',['-o','AuditorV3.olean','AuditorV3.lean']); run('compile-ToyStandard',['-o','ToyStandard.olean','ToyStandard.lean'])
    (build/'ProbeStandard.lean').write_text('import AuditorV3\nimport ToyStandard\n#sol_inventory "standard"\n')
    rows=rows_from(run('inventory-standard',['ProbeStandard.lean']),'standard'); compare_inventory(rows,spec['dependencies'],spec['origin']); assert len(rows)==spec['expectedCleanRows']; reject_custom_axioms(rows)
    catches=[]
    for r in rows:
        assert sorted(r['axioms'])==spec['dependencies'][r['name']],r
        bad={**r,'axioms':['Custom.forbidden']}; catches.append(expect_catch(r['name']+'-forbidden-dependency',reject_custom_axioms,[bad]))
    assert len(catches)==spec['expectedCorruptCatches']
    result={'status':'CONTROLS-PASS','rows':rows,'catches':catches,'processes':processes,'seconds':time.perf_counter()-start}
    (HERE/'standard-axiom-controls-v1.json').write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps({'status':result['status'],'standardAxiomsAccepted':len(rows),'corruptCatches':len(catches),'seconds':result['seconds']}))
if __name__=='__main__': main()
