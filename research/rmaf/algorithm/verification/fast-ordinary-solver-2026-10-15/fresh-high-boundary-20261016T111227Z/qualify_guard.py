#!/usr/bin/env python3
"""Tiny pre-proof resource controls, using scaled rejection thresholds."""
import hashlib, json, pathlib, shutil, subprocess, sys, time
here=pathlib.Path(__file__).resolve().parent
guard=here/'bounded_run.py'
producer=here/'resource_producer.py'
common=['--wall','3','--rss-mib','128','--trip-mib','96','--raw-bytes','1048576','--line-bytes','262144','--compressed-bytes','1048576']
cases=[
 ('positive','clean',[],None),
 ('wall','wall',['--wall','0.15'],'WALL_LIMIT'),
 ('raw','raw',['--raw-bytes','65536'],'RAW_LIMIT'),
 ('line','line',['--line-bytes','32768'],'LINE_LIMIT'),
 ('compressed','compressed',['--compressed-bytes','1024'],'COMPRESSED_LIMIT'),
 ('memory','memory',['--rss-mib','64','--trip-mib','40'],'RSS_TRIP_LIMIT'),
 ('child-memory','child-memory',['--rss-mib','96','--trip-mib','72'],'RSS_TRIP_LIMIT'),
 ('child-raw','child-raw',['--raw-bytes','65536'],'RAW_LIMIT'),
 ('missing-rss','clean',['--plant-missing-rss'],'RSS_MEASUREMENT_UNAVAILABLE'),
 ('disk-floor','clean',['--disk-floor-bytes',str(shutil.disk_usage(here).free+1024**3)],'DISK_FLOOR')]
start=time.monotonic()
results=[]
for name,mode,extra,expected in cases:
    runname='cal3-'+name
    cmd=[sys.executable,str(guard),'--name',runname]+common+extra+['--',sys.executable,str(producer),mode]
    run=subprocess.run(cmd,capture_output=True,text=True,timeout=10)
    receipt=json.loads((here/'runs'/runname/'receipt.json').read_text())
    passed=(receipt['reason']==expected and receipt['status']==('ACCEPT' if expected is None else 'REFUSED')
            and run.returncode==(0 if expected is None else 75) and not receipt['cleanup_errors'])
    if name=='positive': passed=passed and receipt['sample_count']>0 and receipt['kernel_peak_rss']>0 and receipt['raw_seen']==11
    if name=='child-memory': passed=passed and len(receipt['observed_pids'])>=2 and receipt['peak_aggregate_rss']<96*1024**2
    if name=='memory': passed=passed and receipt['peak_aggregate_rss']<64*1024**2
    if name=='disk-floor': passed=passed and not receipt['started']
    results.append(dict(case=name,expected=expected,passed=passed,receipt=receipt,driver_stdout=run.stdout,driver_stderr=run.stderr))
    if not passed:
        break
out=dict(version=3,guard_sha256=hashlib.sha256(guard.read_bytes()).hexdigest(),
         elapsed_seconds=time.monotonic()-start,declared_cases=len(cases),executed_cases=len(results),
         all_passed=len(results)==len(cases) and all(r['passed'] for r in results),results=results,
         old_stage_policy_acceptance=False,new_proofs_authorized=False)
out['new_proofs_authorized']=out['all_passed']
(here/'GUARD-QUALIFICATION-v3.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='results'}))
raise SystemExit(0 if out['all_passed'] else 1)
