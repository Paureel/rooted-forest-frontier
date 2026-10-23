#!/usr/bin/env python3
"""One-shot formal family-assembly arm replay; intentionally project-local.

Builds allowed old dependencies into this arm's own output directory, compiles
its theorem and controls, then requires an explicit false-proposition failure
and the matching positive twin. It does not certify the whole G2 interface.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
RESULTS = ROOT / 'research/rmaf/results'
BUILD = HERE / 'build'
BUILD.mkdir(exist_ok=True)
ENV = dict(os.environ, LEAN_PATH=str(BUILD))
LEAN = ROOT / 'bootloops-lean'
records = []

def run(name, source, output=None, false_control=False):
    args = [str(LEAN)]
    if output is not None:
        args += ['-o', str(BUILD / output)]
    args += [str(source)]
    started = time.monotonic()
    proc = subprocess.run(args, cwd=ROOT, env=ENV, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - started
    log = RESULTS / f'triple-family-cost-replay-{name}.log'
    log.write_text(proc.stdout)
    axioms = sorted(set(a for line in proc.stdout.splitlines()
                        if 'depends on axioms:' in line
                        for a in re.search(r'\[([^]]*)\]', line).group(1).split(', ') if a))
    errors = [line for line in proc.stdout.splitlines() if ': error' in line]
    if false_control:
        passed = (proc.returncode != 0 and len(errors) == 2
                  and proc.stdout.count('is false') == 2
                  and 'cherryClosed.blockCount = 1' in proc.stdout
                  and 'adjacentSameColor.blockCount = 1' in proc.stdout)
    else:
        passed = (proc.returncode == 0 and not errors
                  and set(axioms) <= {'propext', 'Quot.sound', 'Classical.choice'})
    records.append(dict(name=name, exit_code=proc.returncode,
                        elapsed_seconds=elapsed, passed=passed,
                        expected_failure=false_control, axioms=axioms,
                        log=str(log.relative_to(ROOT))))
    if not passed:
        raise RuntimeError(f'{name} failed its declared gate; see {log}')

version = subprocess.run([str(LEAN), '--version'], cwd=ROOT, env=ENV,
                         text=True, capture_output=True, check=True).stdout.strip()
assert '4.35.0' in version, version
sources = [ROOT / 'research/rmaf/triple_dp/TripleDP.lean',
           ROOT / 'research/rmaf/triple_dp/ConnectedRegions.lean',
           HERE / 'FamilyAssembly.lean', HERE / 'Controls.lean',
           HERE / 'CleanTwin.lean', HERE / 'FalseMutant.lean']
for source in sources:
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', source.read_text()), source
run('triple', sources[0], 'TripleDP.olean')
run('connected', sources[1], 'ConnectedRegions.olean')
run('assembly', sources[2], 'FamilyAssembly.olean')
run('controls', sources[3], 'Controls.olean')
run('clean-twin', sources[4])
run('false-mutant', sources[5], false_control=True)
receipt = dict(
    status='CLOSED-UNVERIFIED for three assembly constructors; whole G2 OPEN',
    engine=version,
    scope=['closeBoth', 'extendLeft', 'extendRight',
           'actual finite family invariant', 'cardinality and closed-index cost',
           'per-index leaf-label preservation'],
    remaining=['universal merge', 'restriction/completeness', 'trimming',
               'leafless-fragment discard', 'mask/color legality and DP interface',
               'graph agreement forest correspondence',
               'fresh nonauthor semantic/axiom/control verification'],
    controls={
        'T1':'two child singleton families: count=2, cost=2, root unused',
        'T2':'manual merged cherry fixture: count=1, open cost=0, finished cost=1; not universal merge evidence',
        'T3':'left/right extension: count=2, cost=1',
        'T4':'distinct leaf labels with same color metadata: adjacent supports remain two indices',
        'T5':'singleton: count=1, open cost=0, finished cost=1',
        'regressions':'gapped support and leafless incursion address predicates; not fresh holdout or full family incursion verification',
        'M1_M2':'two explicit false count-one propositions rejected; both count-two twins accepted'},
    runs=records,
    hashes={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sources + [HERE / 'replay.py',
                                ROOT / 'research/rmaf/triple_dp/FAMILY-TARGET.md']})
receipt_path = RESULTS / 'triple-family-cost-replay.json'
receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
print(f'PASS: {len(records)} declared replay stages; 2/2 false propositions rejected and 2/2 clean twins accepted.')
print(f'Receipt: {receipt_path}')
print('Scope: three actual-family assembly constructors; independent acceptance and full G2 remain open.')
