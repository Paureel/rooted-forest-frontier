#!/usr/bin/env python3
"""One-shot preproof control freeze; wrapper around completed state artifacts.

The toolkit has no general Lean proof package. This extends the completed
state-reduction source-bound replay rather than adding a toolkit instrument.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,time,datetime
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
MANIFEST=HERE.parent/'state_reductions/STATE-MANIFEST-v1.json'
PIN=HERE/'CONTROLS-PIN-v1.json'
OUT=HERE/'preproof'
OUT.mkdir(exist_ok=False)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads(MANIFEST.read_text())
assert len(manifest['immutable_files']) == 77
for x in manifest['immutable_files']:
    assert sha(ROOT/x['path']) == x['sha256'], x['path']
MODS=['RMAF','StateRestriction','StateEmbedding','StatePartition','State',
      'Singleton','Removal','Forward','LeafClear','Reverse','CherryGraph','CherryTopology']
FROZEN=ROOT/'results/algorithm-universal233-state-20261015T094847Z'
SOURCES={n:FROZEN/(n+'.lean') for n in MODS}
SOURCES.update({n:HERE/(n+'.lean') for n in ['GraphControls','GraphFalseControls']})
pin={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
     'state_manifest_sha256':sha(MANIFEST),
     'input_hashes':{str(p.relative_to(ROOT)):sha(p) for p in SOURCES.values()},
     'target_sha256':sha(HERE/'TARGET-v1.md'),'positive_required':19,'negative_required':4,
     'status':'PINNED_BEFORE_NEW_PROOF'}
PIN.write_text(json.dumps(pin,indent=2)+'\n')
for n,p in SOURCES.items(): (OUT/(n+'.lean')).write_bytes(p.read_bytes())
env=dict(os.environ,LEAN_PATH=str(OUT))
record={'status':'RUNNING','created_utc':pin['created_utc'],'pin_sha256':sha(PIN),'builds':[]}
def run(n,build=False):
    start=time.monotonic()
    args=[str(ROOT/'bootloops-lean')]
    if build: args+=['-o',str(OUT/(n+'.olean'))]
    p=subprocess.run(args+[str(OUT/(n+'.lean'))],cwd=OUT,env=env,text=True,
        stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
    (OUT/(n+'.log')).write_text(p.stdout)
    record['builds'].append({'module':n,'seconds':time.monotonic()-start,'returncode':p.returncode})
    (OUT/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
    return p
for n in MODS+['GraphControls']:
    p=run(n,True)
    assert p.returncode==0,(n,p.stdout)
p=run('GraphFalseControls')
assert p.returncode!=0 and p.stdout.count('is false')==4,p.stdout
for rel,h in pin['input_hashes'].items(): assert sha(ROOT/rel)==h
record.update(status='PASS_PREPROOF_CONTROLS',positive_examples=19,negative_caught=4,
              universal_proof=False,independent_implementation=False,
              all_three_main_milestones='OPEN')
(OUT/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='builds'},indent=2))
