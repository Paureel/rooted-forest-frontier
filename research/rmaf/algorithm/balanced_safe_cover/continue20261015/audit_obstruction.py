#!/usr/bin/env python3
"""One-shot source-bound finite obstruction replay, not a tree theorem audit."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
from time import perf_counter

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BUILD = HERE/'lean'/'isolated-obstruction'
BUILD.mkdir(exist_ok=True)
rows = []
started = perf_counter()
for name, negative, expected in [('AllRowObstruction', False, 7), ('FalseAllRow', True, 0)]:
    source = HERE/'lean'/f'{name}.lean'
    raw = source.read_bytes()
    assert not re.search(rb'\b(?:sorry|admit|native_decide)\b|^\s*axiom\s', raw, re.M)
    isolated = BUILD/source.name
    shutil.copyfile(source, isolated)
    command = [str(ROOT/'bootloops-lean'), str(isolated)]
    if not negative:
        command += ['-o', str(BUILD/f'{name}.olean')]
    begin = perf_counter()
    proc = subprocess.run(command, cwd=BUILD, env={**os.environ, 'LEAN_PATH': str(BUILD)},
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    elapsed = perf_counter() - begin
    log = BUILD/f'{name}.log'
    log.write_text(proc.stdout)
    axiom_reports = [x for x in proc.stdout.splitlines() if 'axioms' in x]
    axioms = set()
    for match in re.finditer(r'depends on axioms:\s*\[([^]]*)\]', proc.stdout, re.S):
        axioms.update(x.strip() for x in match.group(1).split(',') if x.strip())
    passed = (proc.returncode != 0 and 'proved that the proposition' in proc.stdout and 'is false' in proc.stdout) if negative else (
        proc.returncode == 0 and len(axiom_reports) == expected and axioms <= {'propext', 'Classical.choice', 'Quot.sound'} and 'sorryAx' not in proc.stdout)
    rows.append({'name': name, 'source': str(source.relative_to(ROOT)),
                 'source_sha256': hashlib.sha256(raw).hexdigest(),
                 'isolated_input_sha256': hashlib.sha256(isolated.read_bytes()).hexdigest(),
                 'command': command, 'returncode': proc.returncode, 'expected_negative': negative,
                 'passed': passed, 'axiom_reports': axiom_reports, 'axioms': sorted(axioms),
                 'log': str(log.relative_to(ROOT)), 'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest(),
                 'seconds': elapsed})
report = {'kind': 'GLOBAL-CB3-source-bound-finite-obstruction-audit',
          'date': datetime.now(timezone.utc).isoformat(),
          'verdict': 'SCOPED-KERNEL-REPLAY-PASS' if all(r['passed'] for r in rows) else 'FAILED',
          'kernel_statements': 7, 'false_controls_expected': 1,
          'false_controls_rejected': sum(r['passed'] and r['expected_negative'] for r in rows),
          'scope': 'literal26 cost profiles, at-least-three unit costs, exact rational cross products; original-tree extraction not formalized',
          'rows': rows, 'seconds': perf_counter() - started,
          'audit_script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
dest = ROOT/'research/rmaf/results/algorithm-balanced-cover-continue-cb3-lean-obstruction.json'
dest.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'receipt': str(dest), 'verdict': report['verdict'],
                  'kernel_statements': 7, 'false_controls_rejected': report['false_controls_rejected'],
                  'seconds': report['seconds']}))
if not all(r['passed'] for r in rows):
    raise SystemExit(1)
