"""One-shot mutation audit: deliberately disable the numeric-claim detector."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

here = Path(__file__).resolve().parent
source = here / 'graph_checker.py'
mutant = here / 'graph_checker_numeric_blind_PLANTED.py'
needle = 'if claimed[field] != measured[field]:'
replacement = "if field not in ['blocks', 'cost'] and claimed[field] != measured[field]:"
original = source.read_text()
assert original.count(needle) == 1
mutant.write_text(original.replace(needle, replacement))
receipt = Path('results/triple-family-transitions-adversary-checker-plant-inner.json')
command = [sys.executable, str(here / 'run_adversary.py'), '--mode', 'controls',
           '--checker', str(mutant), '--output', str(receipt)]
start = time.perf_counter()
proc = subprocess.run(command, capture_output=True, text=True)
inner = json.loads(receipt.read_text())
wrong_rows = [r for r in inner['controls']['items'] if r['group'] == 'wrong_result']
passed = (proc.returncode == 1 and inner['verdict'] == 'CONTROL-FAILURE'
          and len(wrong_rows) == 4 and all(not r['passed'] for r in wrong_rows)
          and all(r['clean_twin_passed'] for r in wrong_rows))
result = {'plant': 'Copy disables only numeric-claim mismatch detection',
          'passed': passed, 'command': command, 'exit_code': proc.returncode,
          'stdout': proc.stdout, 'stderr': proc.stderr,
          'mutant_sha256': hashlib.sha256(mutant.read_bytes()).hexdigest(),
          'original_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
          'audit_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'receipt': str(receipt), 'wrong_detector_misses': len(wrong_rows),
          'clean_twins_passed': sum(r['clean_twin_passed'] for r in wrong_rows),
          'elapsed_seconds': time.perf_counter() - start}
out = Path('results/triple-family-transitions-adversary-checker-plant.json')
out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(json.dumps(result, sort_keys=True))
raise SystemExit(0 if passed else 1)
