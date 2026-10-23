#!/usr/bin/env python3
"""One-shot full-path CLI plant: conflicting triple optimum 2 components.
The corrupted source duplicates 0 and must fail parsing; clean twin succeeds.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
started = time.perf_counter()
good = subprocess.run([str(ROOT/'bootloops-python'),str(HERE/'state_cli.py'),str(HERE/'cli-input-v1.json')],
                      cwd=ROOT,text=True,capture_output=True)
assert good.returncode == 0,good.stderr
answer = json.loads(good.stdout)
assert answer['components'] == 2 and answer['additional_cuts'] == 1
assert answer['tested_budgets'] == [0,1]
bad = subprocess.run([str(ROOT/'bootloops-python'),str(HERE/'state_cli.py'),str(HERE/'cli-corruption-v1.json')],
                     cwd=ROOT,text=True,capture_output=True)
assert bad.returncode != 0 and 'duplicate label' in bad.stderr
report = dict(status='full-path-CLI-plant-and-corruption-passed',answer=answer,
              corrupted_exit=bad.returncode,corruption_error=bad.stderr,
              elapsed_seconds=time.perf_counter()-started,
              hashes={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in
                      [Path(__file__),HERE/'state_cli.py',HERE/'cli-input-v1.json',HERE/'cli-corruption-v1.json']})
dest = HERE.parents[1]/'results'/'algorithm-cover-cli-controls-v1.json'
assert not dest.exists(),dest
dest.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(output=str(dest),status=report['status'],elapsed_seconds=report['elapsed_seconds'])))
