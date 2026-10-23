#!/usr/bin/env python3
"""One-shot outer gate: original must pass; numeric-blind copy must fail."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
p = argparse.ArgumentParser()
p.add_argument('--outdir', required=True)
args = p.parse_args()
out = Path(args.outdir)
out.mkdir(parents=True, exist_ok=False)
t0 = time.perf_counter()
records = []
for label, script in [('original', 'exact_restriction_v1.py'), ('numeric_blind_copy', 'exact_restriction_v1_numeric_blind.py')]:
    proc = subprocess.run([str(ROOT / 'bootloops-python'), str(HERE / script), 'controls',
                           '--out', str(out / (label + '.json'))], capture_output=True, text=True, cwd=ROOT)
    (out / (label + '.stdout')).write_text(proc.stdout)
    (out / (label + '.stderr')).write_text(proc.stderr)
    records.append({'label': label, 'returncode': proc.returncode})
original = json.loads((out / 'original.json').read_text())
mutant = json.loads((out / 'numeric_blind_copy.json').read_text())
wrong_rows = [r for r in mutant['rows'] if r['type'] == 'wrong_numbers']
expected_failed_ids = {r['id'] for r in wrong_rows}
checks = {
 'original_passes_all_controls': original['verdict'] == 'PASS' and records[0]['returncode'] == 0,
 'mutant_all_five_wrong_numbers_escape': len(wrong_rows) == 5 and all(not r['wrong_detected'] for r in wrong_rows),
 'mutant_all_wrong_number_clean_twins_pass': all(r['clean_twin_pass'] for r in wrong_rows),
 'mutant_outer_control_gate_rejected': mutant['verdict'] == 'FAIL' and records[1]['returncode'] == 1,
 'mutant_failure_set_exact': set(mutant['failures']) == expected_failed_ids,
}
report = {'verdict': 'PASS' if all(checks.values()) else 'FAIL', 'checks': checks,
          'subprocesses': records, 'elapsed_seconds': time.perf_counter() - t0,
          'manifest_sha256': hashlib.sha256((HERE / 'PRE-RUN-PINS-v1.json').read_bytes()).hexdigest(),
          'original_receipt': str(out / 'original.json'), 'numeric_blind_receipt': str(out / 'numeric_blind_copy.json')}
(out / 'outer-gate.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
print(json.dumps(report, sort_keys=True))
raise SystemExit(0 if report['verdict'] == 'PASS' else 1)
