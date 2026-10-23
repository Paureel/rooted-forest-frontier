#!/usr/bin/env python3
"""One-shot theorem-build recorder for this proof arm, not a general toolkit.

Run via ./bootloops-python .../run_checks.py controls|proof. Every invocation
snapshots its inputs, builds from empty oleans, and retains every result.
Only expected kernel rejection is a passing negative control; malformed
input rejection is recorded separately from false-theorem rejection.
"""
from pathlib import Path
import datetime as dt
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[7]
ROUTE = Path(__file__).resolve().parent
PHASE = sys.argv[1]
assert PHASE in {'controls', 'proof'}
stamp = dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
out = ROOT / 'research/rmaf/results' / ('triple-family-transitions-restriction-normalized-' + stamp)
src, obj = out / 'source', out / 'olean'
src.mkdir(parents=True); obj.mkdir()
base = ROOT / 'research/rmaf/triple_dp'
deps = [base/'TripleDP.lean', base/'ConnectedRegions.lean',
 base/'family/FamilyModel.lean', base/'family/FamilyTrim.lean',
 base/'family/path_route/PathStem.lean', base/'family/FamilyGeometry.lean',
 base/'family/cost_route/FamilyAssembly.lean', base/'family/FamilyTransport.lean',
 base/'family/transitions/FiniteSelection.lean',
 base/'family/transitions/restriction/RestrictionDefs.lean']
targets = [('ControlClean', 0, None), ('ControlFalse', 1, 'decide'),
           ('ControlMalformed', 1, 'Unknown identifier')]
if PHASE == 'proof':
    targets += [('NormalizedRestriction', 0, None), ('RawIncursion', 0, None),
                ('FalseRawPremise', 1, 'Type mismatch')]
paths = deps + [ROUTE/(n+'.lean') for n, _, _ in targets]
pins = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
spec_paths = [ROUTE/'CONTROLS.md', ROUTE.parent/'TARGET.md',
 ROOT/'research/rmaf/results/triple-family-transitions-restriction-adversary-hunt-v1.json']
spec_pins = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in spec_paths}
for p in paths:
    if p.parent == ROUTE:
        assert not re.search(r'(?m)^\s*(?:axiom|constant)\b|\bsorry\b|\badmit\b|\bnative_decide\b', p.read_text()), p
for p in paths: shutil.copyfile(p, src/p.name)
for p in [ROUTE/'CONTROLS.md', ROUTE/'WORK.md', ROUTE/'run_checks.py']:
    shutil.copyfile(p, src/p.name)
receipt = {'phase': PHASE, 'started_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
 'source_sha256': pins, 'spec_sha256': spec_pins,
 'new_source_forbidden_declaration_scan': 'PASS',
 'build_root': str(out), 'rows': [], 'verdict': 'RUNNING',
 'independence': 'Author route only. Old dependencies shared; FiniteSelection compiled opaquely. No new restriction proof bodies imported. Fresh review pending.'}
receipt_path = out/'receipt.json'
def save(): receipt_path.write_text(json.dumps(receipt, indent=2)+'\n')
save()
env = os.environ.copy()
env['ELAN_HOME'] = str(ROOT/'.runtime/elan')
env['LEAN_PATH'] = str(obj)
version = subprocess.run([str(ROOT/'bootloops-lean'), '--version'], cwd=ROOT, env=env,
                         capture_output=True, text=True, timeout=30)
receipt['lean_version'] = version.stdout.strip()
assert version.returncode == 0 and '4.35.0' in version.stdout
all_targets = [(p.stem, 0, None) for p in deps] + targets
for name, expected, token in all_targets:
    start = time.perf_counter()
    cmd = [str(ROOT/'bootloops-lean'), '-o', str(obj/(name+'.olean')), str(src/(name+'.lean'))]
    result = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True, timeout=60)
    log = result.stdout + result.stderr
    (out/(name+'.log')).write_text(log)
    axioms = []
    for match in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
        values = [x.strip() for x in match.group(2).split(',') if x.strip()]
        axioms.append({'declaration': match.group(1), 'axioms': values, 'count': len(values)})
    for match in re.finditer(r"'([^']+)' does not depend on any axioms", log):
        axioms.append({'declaration': match.group(1), 'axioms': [], 'count': 0})
    passed = (result.returncode == 0 if expected == 0 else result.returncode != 0)
    if token is not None: passed = passed and token.lower() in log.lower()
    if expected == 0: passed = passed and 'sorryAx' not in log
    receipt['rows'].append({'module': name, 'returncode': result.returncode,
      'expected': 'compile' if expected == 0 else 'reject', 'diagnostic_token': token,
      'seconds': time.perf_counter()-start, 'passed': passed, 'axiom_reports': axioms})
    print(name, 'PASS' if passed else 'FAIL', flush=True)
    save()
    if not passed:
        receipt['verdict'] = 'FAIL'; save()
        print(log[-6000:], flush=True)
        sys.exit(1)
receipt['verdict'] = 'AUTHOR-CHECK-PASS'
receipt['finished_utc'] = dt.datetime.now(dt.timezone.utc).isoformat()
save()
print(receipt_path)
