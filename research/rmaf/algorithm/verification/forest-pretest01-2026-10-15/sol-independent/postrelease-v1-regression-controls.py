#!/usr/bin/env python3
"""Targeted synthetic regression after the postcontact metadata extension.
Reuses frozen plants, adds no blind replication credit.
"""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
import traceback

HERE=Path(__file__).resolve().parent
BUILD=HERE/'postrelease-v1-scientific'
LEAN=Path('/Users/paurel/Documents/ChatGPT/bootscience/.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean')
spec=importlib.util.spec_from_file_location('frozen_producer_controls',HERE/'producer_controls-v3.py')
frozen=importlib.util.module_from_spec(spec);spec.loader.exec_module(frozen)
result={'phase':'postcontact_metadata_regression','commands':[],'controls':[]};start=time.perf_counter()
out=HERE/'postrelease-v1-regression-controls.json';assert not out.exists()
try:
    assert shutil.disk_usage(HERE).free>=3*2**30
    records=[]
    for letter in ('A','B'):
        modules=['PlantClean','PlantForeign','PlantPrivate','PlantUnused','PlantBodyOnly','PlantCollision'+letter]
        name='PostcontactPlant'+letter
        source=BUILD/(name+'.lean')
        source.write_text('\n'.join('import '+m for m in modules)+'\nimport PostreleaseProducerAuditV2\n'+
                          'audit_selected '+json.dumps(','.join(modules))+'\n')
        environment=dict(os.environ);environment['LEAN_PATH']=str(BUILD)+':'+str(HERE)
        t=time.perf_counter()
        p=subprocess.run([str(LEAN),source.name],cwd=BUILD,env=environment,text=True,capture_output=True,timeout=60)
        result['commands'].append({'name':name,'seconds':time.perf_counter()-t,'timeout_seconds':60,
                                   'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
        assert p.returncode==0
        records.append([json.loads(line[9:]) for line in p.stdout.splitlines() if line.startswith('PRODUCER ')])
    result['controls']=frozen.controls(*records)
    result['status']='PASS'
except BaseException:
    result['status']='FAIL';result['failure']=traceback.format_exc()
finally:
    result['seconds']=time.perf_counter()-start;result['disk_free_after']=shutil.disk_usage(HERE).free
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'controls':len(result['controls']),'seconds':result['seconds'],
                      'disk_free_after':result['disk_free_after']}))
raise SystemExit(0 if result['status']=='PASS' else 1)
