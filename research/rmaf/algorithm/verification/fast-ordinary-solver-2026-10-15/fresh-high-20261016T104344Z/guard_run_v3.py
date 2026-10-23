#!/usr/bin/env python3
"""One-shot target-local runner; not a registered reusable instrument.
Retains bounded Lean output and refuses low disk. Uses existing launcher as-is.
"""
import json, os, pathlib, resource, shutil, subprocess, sys, time

ROOT = pathlib.Path('/Users/paurel/Documents/ChatGPT/bootscience')
HERE = pathlib.Path(__file__).resolve().parent
BUILD = ROOT / 'results/algorithm-universal233-fast-ordinary-recursion-replay-20261015T205325296780Z'
source = HERE / sys.argv[1]
seconds = min(float(sys.argv[2]) if len(sys.argv) > 2 else 30.0, 59.0)
stem = source.stem
log_path = HERE / (stem + '.log')
receipt_path = HERE / (stem + '.receipt.json')
if log_path.exists() or receipt_path.exists():
    raise SystemExit('REFUSED existing evidence path; use a new source basename')
if shutil.disk_usage(HERE).free < 3 * 1024**3:
    raise SystemExit('REFUSED live disk below 3 GiB')
env = os.environ.copy()
env['LEAN_PATH'] = str(HERE) + ':' + str(BUILD)
args = [str(ROOT / 'bootloops-lean'), '-M', '2048', str(source)]
if '--object' in sys.argv:
    args[1:1] = ['-o', str(HERE / (stem + '.olean'))]
start = time.monotonic()
with log_path.open('xb') as log:
    proc = subprocess.Popen(args, stdout=log, stderr=subprocess.STDOUT, env=env, cwd=ROOT, start_new_session=True)
    failure = None
    while proc.poll() is None:
        if time.monotonic() - start > seconds:
            failure = 'deadline'
        elif log_path.stat().st_size > 16 * 1024**2:
            failure = 'raw cap'
        elif shutil.disk_usage(HERE).free < 3 * 1024**3:
            failure = 'disk floor'
        if failure:
            os.killpg(proc.pid, 9)
            break
        time.sleep(0.05)
    code = proc.wait()
raw = log_path.read_bytes()
if max(map(len, raw.splitlines()), default=0) > 8 * 1024**2:
    failure = 'line cap'
peak_rss_bytes = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
if sys.platform != 'darwin': peak_rss_bytes *= 1024
if peak_rss_bytes > 3072 * 1024**2: failure = 'measured peak RSS over 3072 MiB'
receipt = dict(source=str(source), command=args, allocation_limit_mib=2048, measured_children_peak_rss_bytes=peak_rss_bytes, elapsed_seconds=time.monotonic()-start,
               returncode=code, guard_failure=failure, bytes=len(raw),
               lean_path=env['LEAN_PATH'], live_free_bytes=shutil.disk_usage(HERE).free)
receipt_path.write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt))
raise SystemExit(0 if code == 0 and failure is None else 1)
