#!/usr/bin/env python3
"""One-shot literal source import-only/body-only adapter positive/false twins."""
import json
import os
from pathlib import Path
import subprocess
import time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[5]
TOY=HERE/'toy-src'
source=(TOY/'Clean.lean').read_text()
base=json.loads((HERE/'toy-Clean-origins-v2.json').read_text())
base={r['name']:r for r in base['records']}
result={'commands':[],'source_literal_gates':[]}
try:
    for kind in ['import','body']:
        cwd=HERE/('toy-literal-'+kind+'-v3')
        expected=(source.replace('import Std\n','import EmptyDependency\n',1) if kind=='import'
                  else source.replace('def publicPayload : Nat := 7\n','def publicPayload : Nat := 8\n',1))
        assert (cwd/'Clean.lean').read_text()==expected, 'literal source gate failed'
        result['source_literal_gates'].append({'kind':kind,'passed':True,'changes':1})
        env={**os.environ,'LEAN_PATH':str(cwd)+os.pathsep+str(TOY)}
        path=HERE/('toy-literal-'+kind+'-origins-v1.json')
        for cmd in [[str(ROOT/'bootloops-lean'),'-o','Clean.olean','Clean.lean'],
                    [str(ROOT/'bootloops-lean'),'--run',str(HERE/'origin_audit_v2.lean'),
                     'Clean',str(path),'Clean']]:
            started=time.perf_counter()
            p=subprocess.run(cmd,cwd=cwd,env=env,text=True,capture_output=True,timeout=30)
            result['commands'].append({'command':cmd,'cwd':str(cwd),'returncode':p.returncode,
             'seconds':time.perf_counter()-started,'stdout':p.stdout,'stderr':p.stderr})
            assert p.returncode==0, 'literal adapter compile/audit failed'
        data=json.loads(path.read_text())
        records={r['name']:r for r in data['records']}
        assert len(records)==data['origin_count']==len(base), 'literal adapter full origin count changed'
        if kind=='import':
            assert records==base, 'literal import changed exact type/body records'
            result['import_exact_records']={'passed':True,'origins':len(base),'normalization':'NONE'}
        else:
            assert records['GateToy.publicPayload']['type']==base['GateToy.publicPayload']['type'], 'false body changed type'
            try:
                assert records==base, 'literal body plant differs'
            except AssertionError as exc:
                result['body_false_twin']={'caught':True,'message':str(exc)}
            else:
                raise AssertionError('literal body false twin survived')
    result['passed']=True
except Exception as exc:
    result['passed']=False; result['failure']=repr(exc)
    raise
finally:
    (HERE/'literal-adapter-control-v1.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'exact_import_origins':len(base),'body_false_twin_caught':True}))
