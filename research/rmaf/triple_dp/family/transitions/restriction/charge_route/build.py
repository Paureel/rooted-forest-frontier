"""One-shot isolated Lean build, retaining every attempted source and log."""
from pathlib import Path
import os, shutil, subprocess, time, json, hashlib, sys
BASE=Path(__file__).resolve().parent
ROOT=Path.cwd()
SNAP=BASE/'isolated'
LOG=BASE/'logs'
SNAP.mkdir(exist_ok=True); LOG.mkdir(exist_ok=True)
mods=[ROOT/'research/rmaf/triple_dp/TripleDP.lean',ROOT/'research/rmaf/triple_dp/ConnectedRegions.lean',ROOT/'research/rmaf/triple_dp/family/cost_route/FamilyAssembly.lean']
mods += [BASE/name for name in (sys.argv[1:] or ['ChargeCore.lean'])]
env=dict(os.environ,ELAN_HOME=str(ROOT/'.runtime/elan'),LEAN_PATH=str(SNAP))
rows=[]
for src in mods:
    old=SNAP/src.name
    if src.parent != BASE and old.exists() and old.read_bytes()==src.read_bytes() and old.with_suffix('.olean').exists():
        continue
    n=1
    while (LOG/f'{src.stem}-{n}.log').exists(): n+=1
    attempt=BASE/'attempts'/f'{src.stem}-{n}'
    attempt.mkdir(parents=True)
    shutil.copy2(src,attempt/src.name); shutil.copy2(src,old)
    start=time.perf_counter()
    run=subprocess.run([str(ROOT/'bootloops-lean'),'-o',str(old.with_suffix('.olean')),str(old)],env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    seconds=time.perf_counter()-start
    (LOG/f'{src.stem}-{n}.log').write_text(run.stdout)
    row={'module':src.name,'attempt':n,'seconds':seconds,'exit':run.returncode,'sha256':hashlib.sha256(src.read_bytes()).hexdigest()}
    rows.append(row); print(json.dumps(row),flush=True)
    if run.returncode:
        print(run.stdout)
        break
path=ROOT/'research/rmaf/results/triple-family-transitions-restriction-charge-build-history.jsonl'
with path.open('a') as out:
    for row in rows: out.write(json.dumps(row)+'\n')
raise SystemExit(rows[-1]['exit'] if rows else 0)
