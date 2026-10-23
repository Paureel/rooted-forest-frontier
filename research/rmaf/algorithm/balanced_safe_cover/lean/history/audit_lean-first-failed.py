#!/usr/bin/env python3
"""One-shot route audit: supplied conditional logic + finite-model counterexample.
No algorithm-generation functionality. Uses local Lean compiler and copies the
unchanged RMAF dependency into an isolated route build directory.
"""
import hashlib, json, os, pathlib, re, shutil, subprocess, time

ROOT = pathlib.Path(__file__).resolve().parents[4]
HERE = pathlib.Path(__file__).resolve().parent
BUILD = HERE / 'lean' / 'build'
OUT = ROOT / 'research/rmaf/results/algorithm-balanced-cover-lean-audit.json'
BUILD.mkdir(exist_ok=True)
env = dict(os.environ, LEAN_PATH=str(BUILD))
reports = []

def run(name, source, output=None, negative=False):
    started = time.monotonic()
    cmd = [str(ROOT/'bootloops-lean'), str(source)]
    if output:
        cmd += ['-o', str(output)]
    proc = subprocess.run(cmd, cwd=BUILD, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - started
    log = BUILD / (name + '.log')
    log.write_text(proc.stdout)
    row = {'name':name,'source':str(source.relative_to(ROOT)),
           'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
           'returncode':proc.returncode,'seconds':elapsed,
           'log':str(log.relative_to(ROOT)),'expected_negative':negative}
    if negative:
        row['passed'] = proc.returncode != 0 and 'proved that the proposition' in proc.stdout and 'is false' in proc.stdout
    else:
        row['axiom_reports'] = [line for line in proc.stdout.splitlines() if 'axioms' in line]
        row['passed'] = proc.returncode == 0 and 'sorryAx' not in proc.stdout
    reports.append(row)
    return row['passed']

dep = ROOT / 'research/rmaf/lean/RMAF.lean'
shutil.copyfile(dep, BUILD/'RMAF.lean')
checks = []
checks.append(run('dependency', BUILD/'RMAF.lean', BUILD/'RMAF.olean'))
for name in ('ConsumerCore','BalancedCounter'):
    source = HERE/'lean'/f'{name}.lean'
    text = source.read_text()
    forbidden = re.findall(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\s', text, re.M)
    if forbidden:
        raise RuntimeError({'forbidden_proof_tokens':forbidden,'source':str(source)})
    checks.append(run(name, source, BUILD/f'{name}.olean'))
for name in ('FalsePrecut','FalseHalfBudget','FalseExponent','FalseCoverage'):
    checks.append(run(name,HERE/'lean'/f'{name}.lean',negative=True))
result = {'kind':'route-author-Lean-constituent-audit','status':'passed' if all(checks) else 'failed',
          'source_model_scope':'finite executable RMAF graph correspondence remains open',
          'conditional_scope':'ExactCompletion fields and safe-cover survival are explicit hypotheses',
          'expected_accepted_route_theorems':24,'reports':reports,
          'false_controls_expected':4,'false_controls_rejected':sum(r['passed'] for r in reports if r['expected_negative']),
          'total_seconds':sum(r['seconds'] for r in reports),
          'audit_script_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'route_theorems':24,'false_controls_rejected':result['false_controls_rejected'],
                  'seconds':result['total_seconds'],'receipt':str(OUT)}))
if not all(checks):
    raise SystemExit(1)
