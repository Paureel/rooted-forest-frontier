#!/usr/bin/env python3
"""Recompile only own frozen component sources, through the qualified guard.
Any resource refusal stops the stage. Ordinary Lean proof errors stop this replay.
"""
import hashlib,json,pathlib,subprocess,sys,time
here=pathlib.Path(__file__).resolve().parent
root=pathlib.Path('/Users/paurel/Documents/ChatGPT/bootscience')
old=here.parent/'fresh-high-20261016T104344Z'
manifest_path=old/'FINAL-MANIFEST-v1.json'
assert hashlib.sha256(manifest_path.read_bytes()).hexdigest()=='0c5c9696fbae3a3ae6b6c4178a722bfe03e57f9ad555c9d55436008c81036d3d'
manifest=json.loads(manifest_path.read_text())
expected={r['path']:r for r in manifest['evidence_files']}
qualification=json.loads((here/'GUARD-QUALIFICATION-v3.json').read_text())
assert qualification['all_passed'] and qualification['new_proofs_authorized']
assert hashlib.sha256((here/'bounded_run.py').read_bytes()).hexdigest()==qualification['guard_sha256']
assert json.loads((here/'EXPORT-QUALIFICATION-v1.json').read_text())['exact_native_roundtrip']
names=['Geometry15','Geometry17','Endpoint18','Forest21','EndpointRight22','Shared23','Restriction25','Boundary26']
records=[]
start=time.monotonic()
for name in names:
    source=(old/(name+'.lean')).read_bytes()
    assert hashlib.sha256(source).hexdigest()==expected[name+'.lean']['sha256']
    with (here/(name+'.lean')).open('xb') as target: target.write(source)
    command=[sys.executable,str(here/'bounded_run.py'),'--name','recheck-'+name,'--wall','30','--',str(root/'bootloops-lean'),'-M','1536','-o',str(here/(name+'.olean')),str(here/(name+'.lean'))]
    run=subprocess.run(command,capture_output=True,text=True,timeout=35)
    receipt=json.loads((here/'runs'/('recheck-'+name)/'receipt.json').read_text())
    record=dict(name=name,source_sha256=hashlib.sha256(source).hexdigest(),receipt=receipt,driver_stdout=run.stdout,driver_stderr=run.stderr)
    if (here/(name+'.olean')).exists(): record['object_sha256']=hashlib.sha256((here/(name+'.olean')).read_bytes()).hexdigest()
    records.append(record)
    if run.returncode!=0 or receipt['status']!='ACCEPT': break
out=dict(version=1,status='RECHECKED' if len(records)==len(names) and all(r['receipt']['status']=='ACCEPT' for r in records) else 'OPEN_RECHECK_FAILURE',
         historical_policy_acceptance=False,elapsed_seconds=time.monotonic()-start,records=records)
(here/'INHERITED-RECHECK-v1.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status=out['status'],recompiled=len(records),declared=len(names),elapsed_seconds=out['elapsed_seconds'],max_live_aggregate_rss=max(r['receipt']['peak_aggregate_rss'] for r in records),historical_policy_acceptance=False)))
raise SystemExit(0 if out['status']=='RECHECKED' else 1)
