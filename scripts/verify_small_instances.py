#!/usr/bin/env python3
"""Re-run existing small controls and a finite cross-check in temporary copies.

The toolkit has no rMAF solver: reuse the archived problem-specific evaluators
and their production comparator. This is a wrapper, not another solver.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

ROOT=Path(__file__).resolve().parents[1]

def execute(name, args, cwd, records):
    started=time.monotonic()
    env=os.environ.copy()
    # The original oracle has an intentional telemetry fallback. Do not import
    # the source dashboard into this temporary experiment or update its state.
    env.pop('PYTHONPATH',None)
    proc=subprocess.run(args,cwd=cwd,env=env,text=True,capture_output=True,timeout=180)
    (records/(name+'.stdout.txt')).write_text(proc.stdout)
    (records/(name+'.stderr.txt')).write_text(proc.stderr)
    row={'name':name,'command':list(map(str,args)),'exit_code':proc.returncode,
         'seconds':time.monotonic()-started,'stdout':name+'.stdout.txt','stderr':name+'.stderr.txt'}
    if proc.returncode:
        print(proc.stdout[-4000:] + proc.stderr[-4000:], file=sys.stderr)
        raise RuntimeError(f'{name} failed ({proc.returncode}); see {records}')
    return row

def copy_direct_files(source,destination):
    destination.mkdir(parents=True,exist_ok=True)
    for p in source.iterdir():
        if p.is_file() and not p.is_symlink() and p.suffix in {'.py','.json','.lean','.toml'}:
            shutil.copy2(p,destination/p.name)

def run(formal=False):
    stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    records=ROOT/'.verification'/stamp;records.mkdir(parents=True)
    rows=[]
    with tempfile.TemporaryDirectory(prefix='rooted-forest-check-') as folder:
        scratch=Path(folder)
        work=scratch/'research/rmaf'
        if formal:
            shutil.copytree(ROOT/'research/rmaf/lean',work/'lean',
                ignore=shutil.ignore_patterns('.lake','*.olean','*.ilean','__pycache__','audit'))
            for name in ['bootloops-python','bootloops-lean','bootloops-lake','activate.sh']:
                shutil.copy2(ROOT/name,scratch/name)
            # Prefer the invoking workspace's installed pinned elan, while
            # preserving the temporary scripts' relative-root calculation.
            local=ROOT/'.runtime/elan'
            if local.exists():
                (scratch/'.runtime').mkdir()
                (scratch/'.runtime/elan').symlink_to(local.resolve(),target_is_directory=True)
            rows.append(execute('scoped-lean',[sys.executable,str(work/'lean/audit.py')],scratch,records))
            shutil.copytree(work/'lean/audit',records/'lean-audit')
        else:
            copy_direct_files(ROOT/'research/rmaf/oracle',work/'oracle')
            copy_direct_files(ROOT/'research/rmaf/verification',work/'verification')
            (work/'results').mkdir();(work/'progress').mkdir()
            corpus='oracle-corpus-n3-n4.json'
            shutil.copy2(ROOT/'research/rmaf/results'/corpus,work/'results'/corpus)
            commands=[
                ('partition-controls',[sys.executable,str(work/'oracle/oracle.py'),'controls']),
                ('partition-comparator-mutation',[sys.executable,str(work/'oracle/mutation_check.py')]),
                ('edge-cut-controls-and-n3-pilot',[sys.executable,str(work/'verification/edge_cut.py'),'--max-n','3']),
                ('finite-two-route-comparison',[sys.executable,str(work/'verification/compare_results.py'),
                    '--oracle',str(work/'results'/corpus),'--output',str(work/'results/comparison.json'),'--plant']),
                ('exact-recurrence-controls',[sys.executable,str(ROOT/'research/rmaf/baseline-recurrence-check.py')]),
            ]
            for name,args in commands:rows.append(execute(name,args,scratch,records))
            shutil.copytree(work/'results',records/'results')
            comparison=json.loads((work/'results/comparison.json').read_text())
            actual_batches=[{'n':batch['n'],'ordered_pairs':batch['ordered_pairs']}
                            for batch in comparison['batches']]
            if (actual_batches != [{'n':3,'ordered_pairs':9},{'n':4,'ordered_pairs':225}]
                    or comparison['ordered_pairs_checked']!=234 or comparison['discrepancies']):
                raise RuntimeError('Finite comparison denominator or result differs from registered n3/n4 coverage')
            (records/'actual-coverage.json').write_text(json.dumps({
                'actual_batches':actual_batches,'actual_ordered_pairs':234,
                'source_comparator_declared_scope':comparison['scope'],
                'source_label_limit':'The preserved original comparator hardcodes n=3..5 in prose. This wrapper supplies only n=3 and n=4; no five-leaf comparison was executed.',
                'status':'finite-regression-only'},indent=2)+'\n')
    receipt={'started_utc':stamp,'status':'passed','mode':'scoped-formal' if formal else 'finite-regression',
             'commands':rows,'scope':'Existing root model only; not the full algorithm.' if formal else 'Known controls and 234 ordered n3/n4 pairs; finite regression only.',
             'lineage':'Archived leaf-partition and edge-cut cores are reused unchanged. Shared definition and Python runtime. These contacted discovery cases are not fresh algorithm certification.',
             'wrapper_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (records/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'passed','mode':receipt['mode'],'commands':len(rows),
        'scope':receipt['scope'],'receipt':str((records/'receipt.json').relative_to(ROOT))}))

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--formal-only',action='store_true')
    args=parser.parse_args()
    run(args.formal_only)
