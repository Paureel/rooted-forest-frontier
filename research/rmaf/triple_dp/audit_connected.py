"""Separate audit for the single-region connectedness supplement.

Preserves the original 28-theorem receipt. Does not assert graph families,
the full MAF correspondence, or refinement of the Python solver.
"""
import hashlib
import json
import os
import pathlib
import re
import subprocess
import time

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[2]
env = dict(os.environ)
env['ELAN_HOME'] = str(ROOT / '.runtime/elan')
env['LEAN_PATH'] = str(HERE)
rows = []
for name in ['TripleDP.lean', 'ConnectedRegions.lean', 'NegativeConnected.lean']:
    source = HERE / name
    negative = name == 'NegativeConnected.lean'
    cmd = [str(ROOT / 'bootloops-lean')]
    if not negative:
        cmd += ['-o', str(source.with_suffix('.olean'))]
    cmd += [str(source)]
    start = time.perf_counter()
    result = subprocess.run(cmd, env=env, cwd=ROOT, capture_output=True, text=True)
    output = result.stdout + result.stderr
    log = HERE / (source.stem + '-connected-audit.log')
    log.write_text(output)
    if negative:
        assert result.returncode != 0 and 'decide' in output and 'false' in output, output
    else:
        assert result.returncode == 0 and 'sorryAx' not in output, output
        assert re.search(r'\b(sorry|admit|native_decide)\b', source.read_text()) is None
        assert re.search(r'^\s*axiom\b', source.read_text(), re.MULTILINE) is None
    axioms = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output)
    for theorem, names in axioms:
        assert set(filter(None, (x.strip() for x in names.split(',')))) <= {'propext', 'Classical.choice', 'Quot.sound'}
    if name == 'ConnectedRegions.lean':
        assert len(axioms) == 8
    rows.append(dict(file=name, negative=negative, returncode=result.returncode,
                     sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                     checked_axioms=axioms, seconds=time.perf_counter()-start,
                     log=str(log.relative_to(ROOT))))
version = subprocess.run([str(ROOT/'bootloops-lean'), '--version'], env=env,
                         cwd=ROOT, capture_output=True, text=True)
assert version.returncode == 0 and '4.35.0' in version.stdout
receipt = dict(status='passed', version=version.stdout.strip(), builds=rows,
               new_theorem_count=8, dependency_theorem_count=19,
               negative_control='caught',
               scope='Path-convex single-region root/child decomposition on binary addresses; not whole region families or MAF/Python correspondence.')
path = HERE.parent/'results/triple-dp-connected-lean.json'
tmp = path.with_suffix('.tmp')
tmp.write_text(json.dumps(receipt, indent=2)+'\n')
tmp.replace(path)
print(json.dumps({k:receipt[k] for k in ['status','new_theorem_count','negative_control']}))
