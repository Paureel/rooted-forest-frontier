#!/usr/bin/env python3
"""Exact pinned-source rebuild, fresh scientific oleans, independent import DAG."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[6]
PAYLOAD=HERE/'pinned-payload'
RECEIPT=PAYLOAD/'results/algorithm-universal233-forest-solver-20261015T114224630584Z'
certificate=json.loads((RECEIPT/'certificate.json').read_text())
catalog=certificate['source_inputs']
assert len(catalog)==143 and len({r['module'] for r in catalog})==143
sha=lambda b:hashlib.sha256(b).hexdigest()
BUILD=HERE/'isolated-build-v1'
ORIGINAL=HERE/'reconstructed-original-source-v1'
mode=sys.argv[1]
statefile=HERE/'source-rebuild-v1.json'
state=json.loads(statefile.read_text()) if statefile.exists() else {'source_records':[],'runs':[]}
if not BUILD.exists():
    BUILD.mkdir();ORIGINAL.mkdir()
    for row in catalog:
        name=row['module'];src=RECEIPT/(name+'.lean');data=src.read_bytes()
        assert sha(data)==row['adapted_sha256'], 'pinned adapted sha mismatch '+name
        (BUILD/(name+'.lean')).write_bytes(data)
        # Reverse ONLY complete import lines, then demand the pinned original
        # digest. This reconstructs original source bytes without live reads.
        text=data.decode()
        for old,new in row.get('adaptations',{}).items():
            text=re.sub(r'^import '+re.escape(new)+r'(?=\s*$)','import '+old,text,flags=re.M)
        original=text.encode()
        rebuilt_original=sha(original)==row['sha256']
        if rebuilt_original: (ORIGINAL/(name+'.lean')).write_bytes(original)
        state['source_records'].append({**row,'actual_adapted_sha256':sha(data),
            'original_reconstructed_exactly':rebuilt_original,'reconstructed_sha256':sha(original)})
    statefile.write_text(json.dumps(state,indent=2)+'\n')
files={r['module']:BUILD/(r['module']+'.lean') for r in catalog}
deps={n:re.findall(r'^import\s+(\S+)',p.read_text(),re.M) for n,p in files.items()}
order=[];seen=set();active=set()
def walk(n):
    if n in seen:return
    assert n not in active,'scientific import cycle'
    active.add(n)
    for d in deps[n]:
        if d in files:walk(d)
        else:assert d in ['Std','Lean'],'unresolved/nonstandard import '+d
    active.remove(n);seen.add(n);order.append(n)
for n in sorted(files):walk(n)
assert len(order)==143
state['independent_topological_order']=order
state['external_import_roots']=sorted({d for ds in deps.values() for d in ds if d not in files})
completed={r['module'] for r in state['runs'] if r['returncode']==0}
if mode=='pilot':wanted=['RMAF','GroupRestriction','GroupEmbedding']
elif mode=='full':wanted=order
else:raise ValueError('pilot or full')
env={**os.environ,'LEAN_PATH':str(BUILD)}
try:
    for n in wanted:
        if n in completed:continue
        row=next(r for r in catalog if r['module']==n)
        assert sha(files[n].read_bytes())==row['adapted_sha256'],'source changed before compile'
        for d in deps[n]:assert d in completed or d in ['Std','Lean'],'dependency not freshly rebuilt '+d
        started=time.perf_counter()
        p=subprocess.run([str(ROOT/'bootloops-lean'),'-o',n+'.olean',n+'.lean'],cwd=BUILD,
                         env=env,text=True,capture_output=True,timeout=30)
        log=HERE/('compile-'+n+'-v1.log')
        log.write_text(p.stdout+p.stderr)
        state['runs'].append({'module':n,'command':[str(ROOT/'bootloops-lean'),'-o',n+'.olean',n+'.lean'],
            'cwd':str(BUILD),'LEAN_PATH':str(BUILD),'source_sha256':sha(files[n].read_bytes()),
            'returncode':p.returncode,'seconds':time.perf_counter()-started,'log':log.name,
            'olean_sha256':sha((BUILD/(n+'.olean')).read_bytes()) if p.returncode==0 else None})
        statefile.write_text(json.dumps(state,indent=2)+'\n')
        assert p.returncode==0,'fresh source compile failure '+n
        completed.add(n)
    state[mode+'_passed']=True
except Exception as exc:
    state['failure']=repr(exc);raise
finally:statefile.write_text(json.dumps(state,indent=2)+'\n')
print(json.dumps({'mode':mode,'compiled':len(completed),'passed':True,
                  'exact_original_reconstructions':sum(r['original_reconstructed_exactly'] for r in state['source_records'])}))
