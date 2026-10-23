#!/usr/bin/env python3
"""Install optional toolkit source at preserved pins without resetting checkouts."""
from pathlib import Path
import json
import subprocess

ROOT=Path(__file__).resolve().parents[1]
config=json.loads((ROOT/'installation.json').read_text())
for name,directory in [('toolkit','bootloops'),('skills','bootloops-skills')]:
    record=config['sources'][name]
    destination=ROOT/directory
    if destination.exists():
        head=subprocess.check_output(['git','-C',str(destination),'rev-parse','HEAD'],text=True).strip()
        if head!=record['commit']:
            raise SystemExit(f'{directory} already exists at {head}; expected {record["commit"]}. Refusing to reset it.')
        print(directory,'already at pinned commit')
        continue
    subprocess.run(['git','clone','--no-checkout',record['url'],str(destination)],check=True)
    subprocess.run(['git','-C',str(destination),'checkout','--detach',record['commit']],check=True)
    print(directory,record['commit'])
print('Toolkit sources ready. Follow their guides for native/runtime dependencies before bootloops-check.')
