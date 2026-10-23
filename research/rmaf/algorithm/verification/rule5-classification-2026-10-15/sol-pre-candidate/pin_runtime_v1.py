#!/usr/bin/env python3
"""Record trusted installed Lean/std anchors without copying any binary."""
import hashlib
import json
from pathlib import Path
import subprocess
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[5]
commands=[]
for flag in ['--version','--print-prefix']:
    p=subprocess.run([str(ROOT/'bootloops-lean'),flag],text=True,capture_output=True,timeout=30,cwd=ROOT)
    assert p.returncode==0
    commands.append({'command':['bootloops-lean',flag],'stdout':p.stdout,'stderr':p.stderr,'returncode':p.returncode})
prefix=Path(commands[1]['stdout'].strip())
paths=[ROOT/'bootloops-lean',prefix/'bin/lean',prefix/'lib/lean/Std.olean',prefix/'lib/lean/Init.olean',prefix/'lib/lean/Lean.olean']
rows=[]
for p in paths:
    h=hashlib.sha256()
    with p.open('rb') as stream:
        for block in iter(lambda:stream.read(4*1024**2),b''):h.update(block)
    rows.append({'path':str(p),'bytes':p.stat().st_size,'sha256':h.hexdigest()})
data={'trusted_installed_standard_libraries':True,'commands':commands,'anchors':rows,
      'scope':'compiler entry and umbrella library anchors only; not a full transitive library-byte manifest. Installed Std/Lean are expressly trusted by the root pin.',
      'copied_binaries':0,'candidate_contact':False}
(HERE/'TRUSTED-RUNTIME-PIN-v1.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({'runtime_anchors':len(rows),'version':commands[0]['stdout'].strip(),'copied_binaries':0}))
