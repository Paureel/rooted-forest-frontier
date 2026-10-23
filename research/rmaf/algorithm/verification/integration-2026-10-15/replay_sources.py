#!/usr/bin/env python3
"""One-shot isolated replay; does not invoke/reuse author audit machinery."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
from time import perf_counter

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
OUT = ROOT / 'research/rmaf/results'
BUILD = HERE / 'isolated'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def strip_comments_strings(source):
    out, i, depth, quoted = [], 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith('/-', i): depth += 1; i += 2
            elif source.startswith('-/', i): depth -= 1; i += 2
            else: i += 1
        elif quoted:
            if source[i] == '\\': i += 2
            elif source[i] == '"': quoted = False; out.append(' '); i += 1
            else: i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        elif source.startswith('/-', i): depth = 1; out.append(' '); i += 2
        elif source[i] == '"': quoted = True; out.append(' '); i += 1
        else: out.append(source[i]); i += 1
    assert depth == 0 and not quoted
    return ''.join(out)

def compile_one(module, expected=0, suffix='fresh'):
    source = BUILD / f'{module}.lean'
    log = BUILD / f'{module}.{suffix}.log'
    assert not log.exists(), str(log)
    env = os.environ.copy()
    env['LEAN_PATH'] = str(BUILD)
    command = [str(ROOT / 'bootloops-lean'), '-o', str(BUILD / f'{module}.olean'), str(source)]
    tick = perf_counter()
    with log.open('w') as stream:
        p = subprocess.run(command, cwd=BUILD, env=env, stdout=stream, stderr=subprocess.STDOUT)
    row = {'module': module, 'source': str(source.relative_to(ROOT)), 'source_sha256': sha(source),
           'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log), 'exit': p.returncode,
           'elapsed_seconds': perf_counter() - tick, 'expected_exit': expected,
           'passed': p.returncode == expected if isinstance(expected, int) else p.returncode != 0}
    return row

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--phase', choices=['pilot', 'sources'], required=True)
    args = parser.parse_args()
    pinned = json.loads((HERE / 'CANDIDATE-PIN.json').read_text())
    modules = pinned['isolated_source_modules']
    for name, r in modules.items():
        assert sha(ROOT / r['copy']) == r['sha256']
        source = strip_comments_strings((ROOT / r['copy']).read_text())
        bad = re.findall(r'\b(?:sorry|admit|axiom|native_decide)\b', source)
        assert not bad, (name, bad)
    if args.phase == 'pilot':
        row = compile_one('RMAF')
        dest = OUT / 'algorithm-integration-fresh-review-lean-pilot-v1.json'
        payload = {'phase': 'pilot', 'all_passed': row['passed'], 'rows': [row], 'source_sha256': sha(Path(__file__))}
    else:
        pilot = json.loads((OUT / 'algorithm-integration-fresh-review-lean-pilot-v1.json').read_text())
        assert pilot['all_passed']
        deps = {name: set(re.findall(r'^import\s+(\w+)', (ROOT / r['copy']).read_text(), re.M)) & set(modules)
                for name, r in modules.items() if name != 'FalseControls'}
        order, done = [], {'RMAF'}
        while len(done) < len(deps):
            ready = sorted(n for n, req in deps.items() if n not in done and req <= done)
            assert ready, (deps, done)
            order.extend(ready)
            done.update(ready)
        projection = {'pilot_seconds': pilot['rows'][0]['elapsed_seconds'],
                      'remaining_modules': len(order),
                      'projection_seconds': pilot['rows'][0]['elapsed_seconds'] * len(order),
                      'assumption': 'same compiler and fixed frozen18-source dependency DAG; one full original RMAF replay times remaining module count, not a scientific runtime theorem'}
        (HERE / 'LEAN-PROJECTION.json').write_text(json.dumps(projection, indent=2) + '\n')
        rows = pilot['rows'][:]
        for name in order:
            row = compile_one(name)
            rows.append(row)
            print(json.dumps({'module': name, 'exit': row['exit'], 'seconds': row['elapsed_seconds']}), flush=True)
            if not row['passed']: break
        all_positive = len(rows) == len(deps) and all(r['passed'] for r in rows)
        if all_positive:
            row = compile_one('FalseControls', expected='nonzero')
            diagnostic = (ROOT / row['log']).read_text()
            row['explicit_false_diagnostics'] = diagnostic.count("Tactic `decide` proved that the proposition")
            row['passed'] = row['passed'] and row['explicit_false_diagnostics'] == 3 and diagnostic.count('is false') == 3
            rows.append(row)
        dest = OUT / 'algorithm-integration-fresh-review-source-replay-v1.json'
        payload = {'created_utc': datetime.now(timezone.utc).isoformat(),
                   'phase': 'frozen source replay', 'all_passed': all_positive and rows[-1]['passed'],
                   'positive_modules': len(deps), 'negative_modules': 1,
                   'rows': rows, 'forbidden_source_tokens': [], 'source_sha256': sha(Path(__file__)),
                   'all_main_milestones': 'OPEN', 'author_audit_reused': False}
    assert not dest.exists()
    dest.write_text(json.dumps(payload, indent=2) + '\n')
    print(json.dumps({'all_passed': payload['all_passed'], 'rows': len(payload['rows'])}))
    raise SystemExit(0 if payload['all_passed'] else 1)

if __name__ == '__main__': main()
