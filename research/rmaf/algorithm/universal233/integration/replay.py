#!/usr/bin/env python3
"""One-shot source-bound integration replay; no frozen author files are modified.

Builds all exact source dependencies in an isolated local receipt directory,
audits every explicit source declaration, and demands three false controls fail.
A pass certifies the retained Lean proofs only. Production coverage, original
cut components, cost/mass/runtime and fresh nonauthor review are separate gates.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BASE = HERE.parent
SPECS = [('RMAF', ROOT / 'research/rmaf/lean/RMAF.lean')]
SPECS += [(n, BASE / 'geometry' / (n + '.lean')) for n in ('Geometry','Bridge','Composition')]
SPECS += [(n, BASE / 'core' / (n + '.lean')) for n in ('CoreGraph','CherryCoarsening','CoreProgram','CoreInvariants')]
SPECS += [(n, HERE / (n + '.lean')) for n in ('SourceBridge','Contraction','Normalization','InitialLift','Suppression','EraseLift','Origins','Branches','CutRecords','Controls')]
NEGATIVE = HERE / 'FalseControls.lean'
ALLOWED = {'Classical.choice','propext','Quot.sound'}


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def clean(text):
    text = re.sub(r'/\-.*?\-/', lambda m: '\n' * m.group().count('\n'), text, flags=re.S)
    return re.sub(r'--[^\n]*', '', text)


def declarations(p):
    scopes, names = [], []
    for line in clean(p.read_text()).splitlines():
        nm = re.match(r'^namespace\s+(\S+)', line)
        if nm:
            scopes.append(nm.group(1))
        elif re.match(r'^end(?:\s+\S+)?\s*$', line):
            if not scopes:
                raise RuntimeError('unmatched namespace end in ' + str(p))
            scopes.pop()
        else:
            dm = re.match(r'^(?:(?:noncomputable|private|protected)\s+)*(?:def|theorem|abbrev|inductive|structure)\s+([A-Za-z0-9_.]+)', line)
            if dm:
                names.append('.'.join(scopes + [dm.group(1)]))
    if scopes:
        raise RuntimeError('unclosed namespace in ' + str(p))
    return names

stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
OUT = HERE / 'replay' / stamp
OUT.mkdir(parents=True, exist_ok=False)
(HERE / 'LATEST-REPLAY.txt').write_text(str(OUT) + '\n')
record = {'grade': 'AUTHOR KERNEL REPLAY; independent nonauthor review pending',
          'production_algorithm_proved': False, 'kernel_checks_passed': False,
          'builds': [], 'declarations': {}, 'hashes': {}}
inputs = [p for _, p in SPECS] + [NEGATIVE, Path(__file__), ROOT / 'bootloops-lean', HERE / 'lean-toolchain']
for p in inputs:
    record['hashes'][str(p.relative_to(ROOT))] = digest(p)
    if p.suffix == '.lean':
        if re.search(r'\b(sorry|admit|axiom|native_decide)\b', clean(p.read_text())):
            raise RuntimeError('forbidden proof escape in ' + str(p))
        (OUT / p.name).write_bytes(p.read_bytes())
(OUT / 'lean-toolchain').write_bytes((HERE / 'lean-toolchain').read_bytes())
ENV = dict(os.environ, LEAN_PATH=str(OUT))


def save():
    (OUT / 'certificate.json').write_text(json.dumps(record, indent=2) + '\n')


def compile_file(name, output=True):
    args = [str(ROOT / 'bootloops-lean')]
    if output:
        args += ['-o', str(OUT / (name + '.olean'))]
    args += [str(OUT / (name + '.lean'))]
    start = time.monotonic()
    run = subprocess.run(args, cwd=ROOT, env=ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = run.stdout
    (OUT / (name + '.log')).write_text(log)
    item = {'module': name, 'exit': run.returncode, 'seconds': round(time.monotonic()-start,6)}
    record['builds'].append(item)
    save()
    return run.returncode, log

for name, source in SPECS:
    code, log = compile_file(name)
    if code or re.search(r'error:|sorryAx|declaration uses .sorry.', log):
        raise SystemExit('FAIL positive source build: ' + name)
    record['declarations'][name] = declarations(source)
all_names = [n for ns in record['declarations'].values() for n in ns]
if len(set(all_names)) != len(all_names):
    raise RuntimeError('duplicate declaration in audit list')
(OUT / 'Audit.lean').write_text('import Controls\n' + '\n'.join('#print axioms ' + n for n in all_names) + '\n')
code, log = compile_file('Audit', False)
if code:
    raise SystemExit('FAIL complete axiom audit elaboration')
reported = {}
for name, deps in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log):
    axioms = {x.strip() for x in deps.split(',') if x.strip()}
    if not axioms <= ALLOWED:
        raise SystemExit('FAIL unapproved axioms: ' + name + ' ' + str(axioms))
    reported[name] = sorted(axioms)
if set(reported) != set(all_names):
    raise SystemExit('FAIL incomplete declaration axiom set')
record['axioms'] = reported
record['explicit_declaration_count'] = len(all_names)
code, log = compile_file('FalseControls', False)
if code == 0 or log.count('is false') != 3:
    raise SystemExit('FAIL three false proposition controls were not all rejected as expected')
record['false_controls_rejected'] = 3
for p in inputs:
    if digest(p) != record['hashes'][str(p.relative_to(ROOT))]:
        raise SystemExit('FAIL source changed during replay: ' + str(p))
record['kernel_checks_passed'] = True
record['meaning'] = 'all explicit declarations in exact copied source stack kernel-checked with only standard axioms; three false controls rejected; full source generator coverage and original cut/mass/runtime remain OPEN'
save()
(OUT / 'SHA256SUMS.json').write_text(json.dumps(record['hashes'], indent=2) + '\n')
verdict = f'PASS: {len(SPECS)} isolated source builds; {len(all_names)} complete explicit-declaration axiom audits; 9 positive controls; 3 rejected false controls'
(OUT / 'VERDICT.txt').write_text(verdict + '\nAUTHOR KERNEL REPLAY ONLY; full production algorithm OPEN; fresh nonauthor review pending\n')
print(verdict)
print('Receipt:', OUT)
