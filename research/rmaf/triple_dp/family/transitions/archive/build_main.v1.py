"""Problem-specific incremental Lean audit; previous family auditor is frozen.

Each invocation preserves a separate source-hashed receipt, including failed
builds. It audits exactly the printed declarations, not all declarations or
the semantic adequacy of the proved statement. Fresh review remains required.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
RESULTS = ROOT / 'research/rmaf/results'


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--source', required=True)
    p.add_argument('--tag', required=True)
    p.add_argument('--dependency', action='store_true')
    p.add_argument('--false-target')
    a = p.parse_args()
    assert re.fullmatch(r'[a-z0-9-]+', a.tag)
    source = ROOT / a.source
    output = RESULTS / ('triple-family-transitions-build-' + a.tag + '.json')
    log_path = HERE / ('build-' + a.tag + '.log')
    assert source.is_file() and source.suffix == '.lean'
    assert not output.exists() and not log_path.exists(), 'preserve prior attempts'
    build = HERE / 'build-main'
    build.mkdir(exist_ok=True)
    env = dict(os.environ, ELAN_HOME=str(ROOT / '.runtime/elan'), LEAN_PATH=str(build))
    version = subprocess.run([str(ROOT/'bootloops-lean'), '--version'], cwd=ROOT,
                             env=env, capture_output=True, text=True)
    assert version.returncode == 0 and '4.35.0' in version.stdout
    command = [str(ROOT / 'bootloops-lean')]
    if a.false_target is None:
        command += ['-o', str(build / source.with_suffix('.olean').name)]
    command += [str(source)]
    start = time.perf_counter()
    run = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True)
    elapsed = time.perf_counter() - start
    log = run.stdout + run.stderr
    log_path.write_text(log)
    text = source.read_text()
    queries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    forbidden = re.findall(r'\b(?:sorry|admit|native_decide)\b', text)
    forbidden += re.findall(r'^\s*(?:(?:private|protected)\s+)?axiom\b', text, re.M)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    axiom_ok = all(set(filter(None, map(str.strip, names.split(',')))) <= allowed
                   for _, names in queries)
    if a.false_target is not None:
        accepted = (run.returncode != 0 and log.count('error:') == 1
                    and 'Tactic `decide` proved that the proposition' in log
                    and 'is false' in log and a.false_target in log)
    else:
        expected = len(re.findall(r'^#print axioms ', text, re.M))
        accepted = (run.returncode == 0 and 'sorryAx' not in log and not forbidden
                    and axiom_ok and len(queries) == expected and expected > 0)
    row = dict(status='accepted' if accepted else 'rejected', version=version.stdout.strip(),
               source=str(source.relative_to(ROOT)), sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
               command=command, seconds=elapsed, returncode=run.returncode,
               dependency=a.dependency, expected_false_target=a.false_target,
               axiom_queries=queries, allowed_axioms=sorted(allowed), forbidden_tokens=forbidden,
               log=str(log_path.relative_to(ROOT)),
               auditor_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    output.write_text(json.dumps(row, indent=2) + '\n')
    print(json.dumps({'status':row['status'], 'source':source.name, 'queries':len(queries),
                      'seconds':elapsed, 'receipt':str(output.relative_to(ROOT))}))
    if not accepted:
        print(log)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
