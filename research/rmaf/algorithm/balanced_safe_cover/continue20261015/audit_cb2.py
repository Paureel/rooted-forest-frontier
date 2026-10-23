#!/usr/bin/env python3
"""One-shot source-bound replay of CB2's eight scoped constraints and two false controls."""
from concurrent.futures import ThreadPoolExecutor
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
BUILD = HERE/'lean'/'isolated'
BUILD.mkdir(exist_ok=True)


def run(name):
    source = HERE/'lean'/f'{name}.lean'
    isolated = BUILD/source.name
    raw = source.read_bytes()
    if re.search(rb'\b(?:sorry|admit|native_decide)\b|^\s*axiom\s', raw, re.M):
        raise AssertionError('forbidden proof source token')
    shutil.copyfile(source, isolated)
    cmd = [str(ROOT/'bootloops-lean'), str(isolated)]
    if name == 'ConstraintCompression':
        cmd += ['-o', str(BUILD/f'{name}.olean')]
    begin = perf_counter()
    proc = subprocess.run(cmd, cwd=BUILD, env={**os.environ, 'LEAN_PATH': str(BUILD)},
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    seconds = perf_counter() - begin
    log = BUILD/f'{name}.log'
    log.write_text(proc.stdout)
    reports = [line for line in proc.stdout.splitlines() if 'axioms' in line]
    axioms = set()
    for match in re.finditer(r'depends on axioms:\s*\[([^]]*)\]', proc.stdout, re.S):
        axioms.update(x.strip() for x in match.group(1).split(',') if x.strip())
    negative = name != 'ConstraintCompression'
    passed = (proc.returncode != 0 and 'proved that the proposition' in proc.stdout
              and 'is false' in proc.stdout) if negative else (
                  proc.returncode == 0 and len(reports) == 8
                  and axioms <= {'propext', 'Classical.choice', 'Quot.sound'}
                  and 'sorryAx' not in proc.stdout)
    return {'name': name, 'source': str(source.relative_to(ROOT)),
            'source_sha256': hashlib.sha256(raw).hexdigest(),
            'isolated_input_sha256': hashlib.sha256(isolated.read_bytes()).hexdigest(),
            'command': cmd, 'returncode': proc.returncode, 'expected_negative': negative,
            'passed': passed, 'axiom_reports': reports, 'axioms': sorted(axioms),
            'log': str(log.relative_to(ROOT)), 'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest(),
            'seconds': seconds}


def main():
    begin = perf_counter()
    with ThreadPoolExecutor(max_workers=3) as pool:
        rows = list(pool.map(run, ['ConstraintCompression', 'FalseCNF', 'FalseMass']))
    report = {'kind': 'GLOBAL-CB2-source-bound-Lean-constituent-audit',
              'verdict': 'SCOPED-KERNEL-REPLAY-PASS' if all(r['passed'] for r in rows) else 'FAILED',
              'date': datetime.now(timezone.utc).isoformat(), 'rows': rows,
              'kernel_statements': 8, 'false_controls_expected': 2,
              'false_controls_rejected': sum(r['passed'] and r['expected_negative'] for r in rows),
              'scope': 'generic finite row implication/union/length plus literal star residual/mass diagnostic; original-tree interpretation and universal DAG bound not formalized',
              'audit_script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'seconds': perf_counter() - begin}
    dest = ROOT/'research/rmaf/results/algorithm-balanced-cover-continue-cb2-lean.json'
    dest.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'receipt': str(dest), 'verdict': report['verdict'],
                      'kernel_statements': 8, 'false_controls_rejected': report['false_controls_rejected'],
                      'seconds': report['seconds']}))
    if not all(r['passed'] for r in rows):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
