#!/usr/bin/env python3
"""One-shot proof/audit driver; a resource refusal permanently stops this stage."""
import argparse,gzip,hashlib,json,pathlib,subprocess,sys
here=pathlib.Path(__file__).resolve().parent
root=pathlib.Path('/Users/paurel/Documents/ChatGPT/bootscience')
p=argparse.ArgumentParser()
p.add_argument('stem')
p.add_argument('--wall',type=float,default=30)
a=p.parse_args()
stop=here/'STAGE-RESOURCE-STOP-v1.json'
if stop.exists(): raise SystemExit('STAGE STOPPED after resource refusal; new target/stage required')
qualification=json.loads((here/'GUARD-QUALIFICATION-v3.json').read_text())
assert qualification['all_passed'] and hashlib.sha256((here/'bounded_run.py').read_bytes()).hexdigest()==qualification['guard_sha256']
assert json.loads((here/'EXPORT-QUALIFICATION-v1.json').read_text())['exact_native_roundtrip']
source=here/(a.stem+'.lean')
cmd=[sys.executable,str(here/'bounded_run.py'),'--name','proof-'+a.stem,'--wall',str(a.wall),'--',str(root/'bootloops-lean'),'-M','1536','-o',str(here/(a.stem+'.olean')),str(source)]
run=subprocess.run(cmd,capture_output=True,text=True,timeout=a.wall+5)
receipt=json.loads((here/'runs'/('proof-'+a.stem)/'receipt.json').read_text())
print(run.stdout,end='')
if run.stderr: print(run.stderr[:3000],file=sys.stderr)
if receipt['status']!='ACCEPT':
    if receipt['reason']!='PRODUCER_FAILURE':
        stop.write_text(json.dumps(dict(resource_failure=receipt,affected_claims='OPEN',no_more_proof_runs=True),indent=2)+'\n')
    data=b''.join(gzip.decompress(pathlib.Path(c['path']).read_bytes()) for c in receipt['chunks'] if c['complete'])
    print(data.decode(errors='replace')[:6000])
raise SystemExit(run.returncode)
